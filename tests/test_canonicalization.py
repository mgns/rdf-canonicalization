"""Manifest-driven W3C RDFC 1.0 test suite.

Reads tests/rdfc10/manifest.jsonld (from https://github.com/w3c/rdf-canon) and
generates three parametrized test functions:

  test_rdfc10_eval     - RDFC10EvalTest: compare N-Quads canonical output
  test_rdfc10_map      - RDFC10MapTest: compare issued blank-node ID map
  test_rdfc10_negative - RDFC10NegativeEvalTest: poison graph must raise TimeoutError
"""

import json
import re
from pathlib import Path

import pytest
import rdflib

from graph_sign_and_verify_c4gai.rdf_canonicalization import RdfCanonicalization, canonicalize

TESTS_DIR = Path(__file__).parent
FIXTURES_DIR = TESTS_DIR / "rdfc10"

# ---------------------------------------------------------------------------
# Manifest loading
# ---------------------------------------------------------------------------

_manifest = json.loads((FIXTURES_DIR / "manifest.jsonld").read_text())

_EVAL_CASES = [
    (e["id"].lstrip("#"), e)
    for e in _manifest["entries"]
    if e["type"] == "rdfc:RDFC10EvalTest"
]
_MAP_CASES = [
    (e["id"].lstrip("#"), e)
    for e in _manifest["entries"]
    if e["type"] == "rdfc:RDFC10MapTest"
]
_NEG_CASES = [
    (e["id"].lstrip("#"), e)
    for e in _manifest["entries"]
    if e["type"] == "rdfc:RDFC10NegativeEvalTest"
]


# ---------------------------------------------------------------------------
# N-Quads parser that preserves blank-node labels
# ---------------------------------------------------------------------------

_QUAD_TOKENS = 4   # token count for a named-graph quad: s p o g
_TRIPLE_TOKENS = 3  # token count for a default-graph triple: s p o


def _parse(path: Path) -> rdflib.Dataset:  # noqa: C901, PLR0912, PLR0915
    """Parse N-Quads into a Dataset, preserving blank-node labels.

    rdflib's default parser renames blank nodes to UUIDs.  We preserve the
    original labels so `sorted(..., key=str)` is stable across runs, and so
    the issued-ID map (test_rdfc10_map) can be compared by original label.
    Named-graph quads are placed in their named context.
    """
    iri_re = re.compile(r"<([^>]*)>")
    bnode_re = re.compile(r"_:(\S+)")
    lit_re = re.compile(r'"((?:[^"\\]|\\.)*)"(?:@([a-zA-Z-]+)|\^\^<([^>]*)>)?')

    g = rdflib.Dataset()
    bnode_cache: dict[str, rdflib.BNode] = {}

    def _bnode(label: str) -> rdflib.BNode:
        if label not in bnode_cache:
            bnode_cache[label] = rdflib.BNode(label)
        return bnode_cache[label]

    def _decode_iri(raw: str) -> str:
        return re.sub(
            r"\\U([0-9A-Fa-f]{8})|\\u([0-9A-Fa-f]{4})",
            lambda m: chr(int((m.group(1) or m.group(2)), 16)),
            raw,
        )

    _esc = {
        '\\"': '"', "\\'": "'", "\\\\": "\\",
        "\\n": "\n", "\\r": "\r", "\\t": "\t", "\\b": "\b", "\\f": "\f",
    }

    def _term(s: str) -> rdflib.term.Node:
        s = s.strip()
        if s.startswith("<"):
            m = iri_re.match(s)
            return rdflib.URIRef(_decode_iri(m.group(1)))
        if s.startswith("_:"):
            m = bnode_re.match(s)
            return _bnode(m.group(1))
        m = lit_re.match(s)
        val = re.sub(
            r"\\(?:\"|'|\\|n|r|t|b|f|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})",
            lambda e: _esc.get(e.group(0)) or chr(int(e.group(0)[2:], 16)),
            m.group(1),
        )
        if m.group(2):
            return rdflib.Literal(val, lang=m.group(2))
        if m.group(3):
            return rdflib.Literal(val, datatype=rdflib.URIRef(_decode_iri(m.group(3))))
        return rdflib.Literal(val)

    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        tokens: list[str] = []
        pos = 0
        while pos < len(line):
            ch = line[pos]
            if ch in " \t.":
                pos += 1
                continue
            if ch == "<":
                end = line.index(">", pos) + 1
            elif line[pos : pos + 2] == "_:":
                m_b = bnode_re.match(line, pos)
                end = m_b.end()
            elif ch == '"':
                i = pos + 1
                while i < len(line):
                    if line[i] == "\\":
                        i += 2
                        continue
                    if line[i] == '"':
                        i += 1
                        break
                    i += 1
                if i < len(line) and line[i] == "@":
                    i += 1
                    while i < len(line) and line[i] not in " \t.":
                        i += 1
                elif i + 1 < len(line) and line[i : i + 2] == "^^":
                    i += 2
                    end_iri = line.index(">", i) + 1
                    i = end_iri
                end = i
            else:
                pos += 1
                continue
            tokens.append(line[pos:end])
            pos = end
        if len(tokens) >= _QUAD_TOKENS:
            ctx = g.get_context(_term(tokens[3]))
            ctx.add((_term(tokens[0]), _term(tokens[1]), _term(tokens[2])))
        elif len(tokens) >= _TRIPLE_TOKENS:
            default_ctx = g.default_graph if hasattr(g, "default_graph") else g.default_context
            default_ctx.add((_term(tokens[0]), _term(tokens[1]), _term(tokens[2])))
    return g


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _normalize(
    graph: rdflib.Dataset,
    max_run_time: float | None = None,
    hash_algorithm: str = "sha256",
    max_work_factor: int | None = None,
) -> list[str]:
    """Return sorted canonical N-Quads lines via the public canonicalize() API."""
    output = canonicalize(
        graph,
        hash_algorithm=hash_algorithm,
        max_run_time=max_run_time,
        max_work_factor=max_work_factor,
    )
    return sorted(line for line in output.splitlines() if line.strip())


def _issued_map(graph: rdflib.Dataset, hash_algorithm: str = "sha256") -> dict[str, str]:
    """Return the issued blank-node ID map {original_label: canonical_id}.

    Keys are the original blank-node label strings (without ``_:`` prefix).
    Values are the canonical ID strings (without ``_:`` prefix, e.g. ``c14n0``).
    """
    c = RdfCanonicalization(graph, hash_algorithm=hash_algorithm)
    _ = c.normalize
    # canon_issuer.ids: {BNode('e0'): '_:c14n0', ...}
    return {str(bn): cid[2:] for bn, cid in c.canon_issuer.ids.items()}


# ---------------------------------------------------------------------------
# Test functions
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(("test_id", "entry"), _EVAL_CASES, ids=[t[0] for t in _EVAL_CASES])
def test_rdfc10_eval(test_id: str, entry: dict) -> None:  # noqa: ARG001
    """RDFC10EvalTest: canonicalize input, compare sorted N-Quads to expected."""
    algo = entry.get("hashAlgorithm", "SHA256")
    graph = _parse(TESTS_DIR / entry["action"])
    actual = _normalize(graph, hash_algorithm=algo)
    expected = sorted(
        line for line in (TESTS_DIR / entry["result"]).read_text().splitlines() if line.strip()
    )
    assert actual == expected


@pytest.mark.parametrize(("test_id", "entry"), _MAP_CASES, ids=[t[0] for t in _MAP_CASES])
def test_rdfc10_map(test_id: str, entry: dict) -> None:  # noqa: ARG001
    """RDFC10MapTest: canonicalize input, compare issued blank-node ID map."""
    algo = entry.get("hashAlgorithm", "SHA256")
    graph = _parse(TESTS_DIR / entry["action"])
    actual = _issued_map(graph, hash_algorithm=algo)
    expected = json.loads((TESTS_DIR / entry["result"]).read_text())
    assert actual == expected


@pytest.mark.parametrize(("test_id", "entry"), _NEG_CASES, ids=[t[0] for t in _NEG_CASES])
def test_rdfc10_negative(test_id: str, entry: dict) -> None:  # noqa: ARG001
    """RDFC10NegativeEvalTest: poison graph must raise TimeoutError."""
    graph = _parse(TESTS_DIR / entry["action"])
    with pytest.raises(TimeoutError):
        _normalize(graph, max_run_time=2.0)


@pytest.mark.parametrize(("test_id", "entry"), _NEG_CASES, ids=[t[0] for t in _NEG_CASES])
def test_rdfc10_negative_work_factor(test_id: str, entry: dict) -> None:  # noqa: ARG001
    """Poison graph must raise TimeoutError when the work-factor limit is hit."""
    graph = _parse(TESTS_DIR / entry["action"])
    with pytest.raises(TimeoutError):
        _normalize(graph, max_work_factor=10)
