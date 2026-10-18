"""RDFC 1.0 (W3C Recommendation 2024) RDF Dataset Canonicalization."""

import argparse
import functools
import hashlib
import itertools
import sys
import timeit
from collections import defaultdict
from collections.abc import Iterator

import rdflib
from rdflib import ConjunctiveGraph, Graph

# Preserve input lexical forms — do not normalise dateTime, integers, etc.
rdflib.NORMALIZE_LITERALS = False

XSD_STRING = rdflib.URIRef("http://www.w3.org/2001/XMLSchema#string")
_DEFAULT_GRAPH_ID = rdflib.URIRef("urn:x-rdflib:default")

_Quad = tuple[rdflib.term.Node, rdflib.URIRef, rdflib.term.Node, rdflib.term.Node | None]
_NQ_CTRL_LIMIT = 0x20  # code points below this require \uXXXX escape in N-Quads
_NQ_DEL = 0x7F  # DELETE also requires \uXXXX


class RdfCanonicalization:
    """RDFC 1.0 (W3C Recommendation 2024) dataset canonicalization.

    Implements the main algorithm (§4.4.3): collect blank nodes, issue
    first-degree singleton canonical IDs, then resolve remaining blank nodes
    via n-degree neighbourhood hashing, and emit sorted canonical N-Quads.
    """

    def __init__(
        self,
        graph: ConjunctiveGraph | Graph,
        max_run_time: float | None = None,
        hash_algorithm: str = "sha256",
        max_work_factor: int | None = None,
    ) -> None:
        self.graph = graph
        self.max_run_time = max_run_time
        self.max_work_factor = max_work_factor
        self._hash_alg = hash_algorithm.lower().replace("-", "")
        self._new_hash = functools.partial(hashlib.new, self._hash_alg)
        self.blank_id_to_quad_set: defaultdict[rdflib.BNode, set[_Quad]] = defaultdict(set)
        self.canon_issuer = IdentifierIssuer()
        self.hash_to_blank_id: defaultdict[str, set[rdflib.BNode]] = defaultdict(set)
        self.non_normalized: set[rdflib.BNode] = set()
        self.start_time: float = 0.0
        self._work_counter: int = 0
        self._max_work: int | None = None

    @property
    def normalize(self) -> str:
        """Run the RDFC 1.0 algorithm and return the canonical N-Quads string."""
        self.start_time = timeit.default_timer()
        self.collect_blank_nodes()
        self.issue_canonical_ids()
        self.issue_n_degree_ids()
        return self.serialize_normalized_graph()

    def _iter_quads(self) -> Iterator[_Quad]:
        """Yield (s, p, o, g) tuples; g is None for the default graph."""
        if isinstance(self.graph, ConjunctiveGraph):
            dg = (
                self.graph.default_graph
                if hasattr(self.graph, "default_graph")
                else self.graph.default_context
            )
            default_id = dg.identifier  # type: ignore[union-attr]
            for s, p, o, ctx in self.graph.quads():
                g = ctx.identifier if hasattr(ctx, "identifier") else ctx  # type: ignore[union-attr]
                yield s, p, o, None if g == default_id else g  # type: ignore[misc]
        else:
            for s, p, o in self.graph:
                yield s, p, o, None  # type: ignore[misc]

    def collect_blank_nodes(self) -> None:
        """RDFC 1.0 §4.4.3 step 3: build blank-node to quad-set index.

        Also computes the permutation-step budget when max_work_factor is set:
        budget = max_work_factor * max(1, number_of_blank_nodes).
        """
        for s, p, o, g in self._iter_quads():
            quad = (s, p, o, g)
            for component in (s, o, g):
                if isinstance(component, rdflib.BNode):
                    self.blank_id_to_quad_set[component].add(quad)
                    self.non_normalized.add(component)
        if self.max_work_factor is not None:
            self._max_work = self.max_work_factor * max(1, len(self.non_normalized))

    def issue_canonical_ids(self) -> None:
        """Issue canonical IDs for unique first-degree hash groups (§4.4.3 steps 4-5).

        Computes HashFirstDegreeQuads once for every non-normalized blank node, groups them
        by hash, then issues canonical IDs for every singleton group (§4.4.3 step 5).
        After this step hash_to_blank_id holds the remaining non-singleton groups, which
        issue_n_degree_ids uses to iterate in first-degree hash order (§4.4.3 step 6).
        """
        self.check_runtime()
        self.hash_to_blank_id.clear()
        for blank_id in self.non_normalized:
            hash_value = self.hash_first_degree(blank_id)
            self.hash_to_blank_id[hash_value].add(blank_id)
        for hash_value, blank_ids in sorted(self.hash_to_blank_id.items()):
            if len(blank_ids) == 1:
                single_blank = next(iter(blank_ids))
                self.canon_issuer.get_id(single_blank)
                self.non_normalized.remove(single_blank)
                del self.hash_to_blank_id[hash_value]

    def issue_n_degree_ids(self) -> None:
        """RDFC 1.0 step 6: n-degree hashing with issuer-order canonical ID assignment.

        Iterates first-degree hash groups in first-degree hash order (spec §4.4.3 step 6),
        then within each group sorts by n-degree hash (§4.4.3 step 6.3.3) and issues
        canonical IDs for every blank node in each result issuer in issuance order.
        """
        for fd_hash in sorted(self.hash_to_blank_id.keys()):
            blank_ids = sorted(self.hash_to_blank_id[fd_hash], key=str)
            issuer_list = []
            for blank_id in blank_ids:
                self.check_runtime()
                issuer = IdentifierIssuer("_:b")
                issuer.get_id(blank_id)
                h, result_issuer = self.hash_n_degree_quads(blank_id, issuer)
                issuer_list.append((h, result_issuer))
            for _, result_issuer in sorted(issuer_list, key=lambda x: x[0]):
                for bn in result_issuer.ids:
                    if not self.canon_issuer.has_id(bn):
                        self.canon_issuer.get_id(bn)
        self.non_normalized.clear()

    def hash_n_degree_quads(  # noqa: C901, PLR0912, PLR0915
        self,
        blank_id: rdflib.BNode,
        issuer: "IdentifierIssuer",
    ) -> tuple[str, "IdentifierIssuer"]:
        r"""HashNDegreeQuads (§4.8): recursively hash the neighbourhood of blank_id.

        Groups related blank nodes by their HashRelatedBlankNode value (§4.7), then
        finds the lexicographically smallest path across all orderings (permutations) of
        each group.  Skips a permutation early once its path prefix exceeds the current
        best (§4.8 step 5.4.4.4 / 5.4.5.4).  Recursion appends the issued temp ID and
        '<hash>' to the path (§4.8 step 5.4.4.3 and 5.4.5.2).
        """
        h_to_bnodes: defaultdict[str, list[rdflib.BNode]] = defaultdict(list)
        for quad in self.blank_id_to_quad_set[blank_id]:
            s, p, o, g = quad
            # position 'g' has no predicate (§4.7)
            for position, component, predicate in (("s", s, p), ("o", o, p), ("g", g, None)):
                if isinstance(component, rdflib.BNode) and component != blank_id:
                    h = self._hash_related_blank_node(component, issuer, predicate, position)
                    h_to_bnodes[h].append(component)

        data_to_hash = ""
        for related_hash in sorted(h_to_bnodes.keys()):
            related_bnodes = h_to_bnodes[related_hash]
            data_to_hash += related_hash

            if len(related_bnodes) == 1:
                # Single-element group: exactly one permutation, no copy needed
                self._work_counter += 1
                if self._max_work is not None and self._work_counter > self._max_work:
                    raise TimeoutError(
                        f"Normalization exceeded work factor limit "
                        f"({self._max_work} permutation steps).",
                    )
                if self.max_run_time and self._work_counter % 256 == 0:
                    self.check_runtime()
                component = related_bnodes[0]
                if (cid := self.canon_issuer.ids.get(component)) is not None or (
                    cid := issuer.ids.get(component)
                ) is not None:
                    chosen_path = cid
                else:
                    chosen_path = issuer.get_id(component)
                    result_hash, issuer = self.hash_n_degree_quads(component, issuer)
                    chosen_path += issuer.ids[component] + "<" + result_hash + ">"
                data_to_hash += chosen_path
                continue

            chosen_path = ""
            chosen_issuer = None
            for permutation in itertools.permutations(sorted(related_bnodes, key=str)):
                self._work_counter += 1
                if self._max_work is not None and self._work_counter > self._max_work:
                    raise TimeoutError(
                        f"Normalization exceeded work factor limit "
                        f"({self._max_work} permutation steps).",
                    )
                if self.max_run_time and self._work_counter % 256 == 0:
                    self.check_runtime()
                issuer_copy = issuer.copy()
                path = ""
                recursion_list: list[rdflib.BNode] = []
                skip = False
                for component in permutation:
                    if (cid := self.canon_issuer.ids.get(component)) is not None or (
                        cid := issuer_copy.ids.get(component)
                    ) is not None:
                        path += cid
                    else:
                        path += issuer_copy.get_id(component)
                        recursion_list.append(component)
                    if chosen_path and path > chosen_path[: len(path)]:
                        skip = True
                        break
                if not skip:
                    for b in recursion_list:
                        result_hash, issuer_copy = self.hash_n_degree_quads(b, issuer_copy)
                        path += issuer_copy.ids[b] + "<" + result_hash + ">"
                        if chosen_path and path > chosen_path[: len(path)]:
                            skip = True
                            break
                if not skip and (not chosen_path or path < chosen_path):
                    chosen_path = path
                    chosen_issuer = issuer_copy
            data_to_hash += chosen_path
            if chosen_issuer:
                issuer = chosen_issuer
        return self._new_hash(data_to_hash.encode("utf-8")).hexdigest(), issuer

    def _hash_related_blank_node(
        self,
        related: rdflib.BNode,
        issuer: "IdentifierIssuer",
        predicate: rdflib.URIRef | None,
        position: str,
    ) -> str:
        r"""HashRelatedBlankNode (§4.7): sha256(position [+ '<predicate>'] + identifier).

        For position 'g' (graph name), no predicate term is included.
        """
        identifier = (
            self.canon_issuer.ids.get(related)
            or issuer.ids.get(related)
            or self.hash_first_degree(related)
        )
        if position == "g":
            return self._new_hash((position + identifier).encode("utf-8")).hexdigest()
        data = (position + f"<{predicate}>" + identifier).encode("utf-8")
        return self._new_hash(data).hexdigest()

    def hash_first_degree(self, blank_id: rdflib.BNode) -> str:
        r"""HashFirstDegreeQuads (§4.6): hash the canonical N-Quads of adjacent quads.

        Each serialized quad ends with ' .\n' and the strings are concatenated
        directly (matching the reference N-Quads serialisation, spec §4.6 step 3.2).
        """
        quads = self.blank_id_to_quad_set[blank_id]
        serialized_quads = sorted(self._serialize_quad_fd(q, blank_id) for q in quads)
        return self._new_hash("".join(serialized_quads).encode("utf-8")).hexdigest()

    def _serialize_quad_fd(self, quad: _Quad, blank_id: rdflib.BNode) -> str:
        r"""Serialize one quad for HashFirstDegreeQuads (§4.6 step 3).

        Replaces blank_id with '_:a', other blank nodes without a canonical ID with '_:z',
        and blank nodes that already have a canonical ID with that ID (§4.6 step 3.1).
        Output ends with ' .\n' so concatenation gives canonical N-Quads form (§4.6 step 3.2).
        """

        def term(t: rdflib.term.Node) -> str:
            if t == blank_id:
                return "_:a"
            if isinstance(t, rdflib.BNode):
                if self.canon_issuer.has_id(t):
                    return self.canon_issuer.ids[t]  # already prefixed "_:c14nN"
                return "_:z"
            if isinstance(t, rdflib.URIRef):
                return f"<{t}>"
            if isinstance(t, rdflib.Literal):
                return _literal_to_nq(t)
            return str(t)

        s, p, o, g = quad
        ts, tp, to = term(s), term(p), term(o)
        if g is not None:
            return f"{ts} {tp} {to} {term(g)} .\n"
        return f"{ts} {tp} {to} .\n"

    def serialize_normalized_graph(self) -> str:
        """RDFC 1.0 §4.4.3 step 7: emit sorted canonical N-Quads for the normalized dataset.

        Replaces each blank node with its canonical ID (§4.3 / §4.5), then sorts all lines
        by Unicode code point order and concatenates them.
        """

        def canon_term(t: rdflib.term.Node) -> str:
            if isinstance(t, rdflib.BNode):
                cid = self.canon_issuer.ids.get(t)
                return cid if cid is not None else f"_:{t}"  # cid already has "_:" prefix
            return _term_nq(t)

        lines = []
        for s, p, o, g in self._iter_quads():
            cs = canon_term(s)
            cp = _term_nq(p)
            co = canon_term(o)
            if g is not None:
                lines.append(f"{cs} {cp} {co} {canon_term(g)} .\n")
            else:
                lines.append(f"{cs} {cp} {co} .\n")
        return "".join(sorted(lines))

    def runtime(self) -> float:
        """Return elapsed wall-clock seconds since canonicalization started."""
        return timeit.default_timer() - self.start_time

    def check_runtime(self) -> None:
        """Raise TimeoutError if the configured max_run_time has been exceeded."""
        if self.max_run_time and (self.runtime() > self.max_run_time):
            raise TimeoutError("Normalization process exceeded the maximum runtime.")


def _escape_literal(s: str) -> str:
    r"""Escape a string value per the N-Quads canonical form (RDF 1.1 §8 / RDFC 1.0 §4.5).

    Named escapes: \\ \" \t \b \n \r \f.  Other U+0000-U+001F and U+007F use \uXXXX.
    """
    result = []
    for ch in s:
        cp = ord(ch)
        if ch == '"':
            result.append('\\"')
        elif ch == "\\":
            result.append("\\\\")
        elif ch == "\t":
            result.append("\\t")
        elif ch == "\b":
            result.append("\\b")
        elif ch == "\n":
            result.append("\\n")
        elif ch == "\r":
            result.append("\\r")
        elif ch == "\f":
            result.append("\\f")
        elif cp < _NQ_CTRL_LIMIT or cp == _NQ_DEL:
            result.append(f"\\u{cp:04X}")
        else:
            result.append(ch)
    return "".join(result)


def _literal_to_nq(lit: rdflib.Literal) -> str:
    """Serialize a Literal to canonical N-Quads form.

    Plain xsd:string literals omit the datatype (RDF 1.1 canonical form).
    """
    escaped = _escape_literal(str(lit))
    body = f'"{escaped}"'
    if lit.language:
        return f"{body}@{lit.language}"
    if lit.datatype and lit.datatype != XSD_STRING:
        return f"{body}^^<{lit.datatype}>"
    return body


def _term_nq(term: rdflib.term.Node) -> str:
    """Serialize a non-blank-node RDF term to canonical N-Quads form (RDFC 1.0 §4.5)."""
    if isinstance(term, rdflib.URIRef):
        return f"<{term}>"
    if isinstance(term, rdflib.Literal):
        return _literal_to_nq(term)
    raise TypeError(f"Unexpected term type: {type(term)!r}")


def canonicalize(
    dataset: rdflib.ConjunctiveGraph | rdflib.Graph | str | bytes,
    *,
    hash_algorithm: str = "sha256",
    max_run_time: float | None = None,
    max_work_factor: int | None = None,
) -> str:
    r"""Canonicalize an RDF dataset using RDFC 1.0 (W3C Recommendation 2024).

    Args:
        dataset: An rdflib Dataset, ConjunctiveGraph, or Graph; or N-Quads text
                 as ``str`` or ``bytes``.  Triples-only graphs are treated as
                 default-graph quads.
        hash_algorithm: Digest algorithm passed to ``hashlib.new()``
                        (default ``"sha256"``; use ``"sha384"`` for the
                        SHA-384 variant defined in the W3C test suite).
        max_run_time: Optional wall-clock limit in seconds.  Raises
                      ``TimeoutError`` if exceeded (protects against
                      poison-graph inputs).
        max_work_factor: Optional machine-independent limit.  The budget is
                         ``max_work_factor * max(1, blank_node_count)``
                         permutation steps.  Raises ``TimeoutError`` when
                         exceeded.  Use alongside or instead of ``max_run_time``.

    Returns:
        Canonical N-Quads string: lines sorted by Unicode code point, each
        ending with ``\n``.

    """
    if isinstance(dataset, str | bytes):
        text = dataset.decode("utf-8") if isinstance(dataset, bytes) else dataset
        graph: rdflib.ConjunctiveGraph | rdflib.Graph = rdflib.ConjunctiveGraph()
        graph.parse(data=text, format="nquads")
    else:
        graph = dataset
    return RdfCanonicalization(
        graph,
        max_run_time=max_run_time,
        hash_algorithm=hash_algorithm,
        max_work_factor=max_work_factor,
    ).normalize


class IdentifierIssuer:
    """Issues deterministic blank-node identifiers in encounter order (RDFC 1.0 §4.3).

    The canonical issuer uses prefix '_:c14n' (IDs: '_:c14n0', '_:c14n1', ...).
    Temporary issuers used during HashNDegreeQuads use prefix '_:b'.
    Iteration order over `ids` is Python dict insertion order, which matches the
    spec's "order in which identifiers were issued" (§4.4.3 step 6.3.4).
    """

    def __init__(self, prefix: str = "_:c14n") -> None:
        self.prefix = prefix
        self.ids: dict[rdflib.BNode, str] = {}
        self._count = 0

    def get_id(self, blank_node: rdflib.BNode) -> str:
        """Return the canonical ID for blank_node, issuing a new one if needed."""
        if blank_node not in self.ids:
            self.ids[blank_node] = f"{self.prefix}{self._count}"
            self._count += 1
        return self.ids[blank_node]

    def has_id(self, blank_node: rdflib.BNode) -> bool:
        """Return True if blank_node has already been issued a canonical ID."""
        return blank_node in self.ids

    def copy(self) -> "IdentifierIssuer":
        """Return a shallow copy of this issuer with the same IDs and counter."""
        new = IdentifierIssuer(self.prefix)
        new.ids = dict(self.ids)
        new._count = self._count  # noqa: SLF001
        return new


def main() -> None:
    """Canonicalize an RDF file to N-Quads on stdout.

    Reads FILE (or stdin), parses with rdflib, applies RDFC 1.0
    canonicalization, and writes sorted N-Quads to stdout.
    """
    parser = argparse.ArgumentParser(
        prog="canonicalize",
        description="RDFC 1.0 RDF Dataset Canonicalization (W3C Recommendation 2024)",
    )
    parser.add_argument(
        "input",
        nargs="?",
        metavar="FILE",
        help="RDF input file; omit or use '-' for stdin",
    )
    parser.add_argument(
        "--format",
        "-f",
        default="nquads",
        dest="fmt",
        metavar="FORMAT",
        help="rdflib input format (default: nquads; e.g. turtle, trig)",
    )
    parser.add_argument(
        "--hash-algorithm",
        "-a",
        default="sha256",
        dest="hash_algorithm",
        metavar="ALGO",
        help="hash algorithm: sha256 (default) or sha384",
    )
    parser.add_argument(
        "--max-run-time",
        "-t",
        type=float,
        default=None,
        dest="max_run_time",
        metavar="SECONDS",
        help="wall-clock timeout in seconds; exits non-zero on timeout",
    )
    parser.add_argument(
        "--max-work-factor",
        "-w",
        type=int,
        default=None,
        dest="max_work_factor",
        metavar="N",
        help="machine-independent limit: N * blank-node-count permutation steps",
    )
    args = parser.parse_args()

    g = rdflib.ConjunctiveGraph()
    try:
        if args.input is None or args.input == "-":
            g.parse(data=sys.stdin.read(), format=args.fmt)
        else:
            g.parse(args.input, format=args.fmt)
        result = canonicalize(
            g,
            hash_algorithm=args.hash_algorithm,
            max_run_time=args.max_run_time,
            max_work_factor=args.max_work_factor,
        )
    except TimeoutError as exc:
        sys.exit(f"canonicalize: timeout: {exc}")
    except Exception as exc:  # noqa: BLE001
        sys.exit(f"canonicalize: error: {exc}")
    sys.stdout.write(result)
