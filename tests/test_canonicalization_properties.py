"""Property-based tests for RDFC 1.0 canonicalization.

Invariants under test:
  - Blank-node relabeling: renaming all blank nodes via any bijection
    must produce identical canonical output.
  - Quad-order invariance: inserting quads in a different order must
    produce identical canonical output.
  - Idempotency: canonicalizing twice yields the same string.
"""

from __future__ import annotations

import random

import rdflib
from hypothesis import given, settings
from hypothesis import strategies as st

from graph_sign_and_verify_c4gai.rdf_canonicalization import canonicalize

# ---------------------------------------------------------------------------
# Strategies
# ---------------------------------------------------------------------------

# Safe IRI characters that never need escaping in N-Quads
_SAFE_CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-"

_iris = st.builds(
    lambda s: rdflib.URIRef(f"http://example.org/{s}"),
    st.text(_SAFE_CHARS, min_size=1, max_size=12),
)

_bnode_labels = st.text(_SAFE_CHARS, min_size=1, max_size=8)

_bnodes = st.builds(rdflib.BNode, _bnode_labels)

_plain_literals = st.builds(
    rdflib.Literal,
    st.text(
        st.characters(
            whitelist_categories=("Lu", "Ll", "Nd"),
            whitelist_characters=" ",
        ),
        max_size=20,
    ),
)

_subjects = st.one_of(_iris, _bnodes)
_objects = st.one_of(_iris, _bnodes, _plain_literals)

_Triple = tuple[rdflib.term.Node, rdflib.URIRef, rdflib.term.Node]


def _triple_st() -> st.SearchStrategy[_Triple]:
    return st.tuples(_subjects, _iris, _objects)


def _graph_st(
    max_triples: int = 8,
) -> st.SearchStrategy[rdflib.ConjunctiveGraph]:
    """Strategy that builds a ConjunctiveGraph from a list of triples."""
    return st.builds(
        _build_graph,
        st.lists(_triple_st(), max_size=max_triples),
    )


def _build_graph(triples: list[_Triple]) -> rdflib.ConjunctiveGraph:
    g = rdflib.ConjunctiveGraph()
    for s, p, o in triples:
        g.add((s, p, o))
    return g


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _relabel(
    g: rdflib.ConjunctiveGraph,
    mapping: dict[str, str],
) -> rdflib.ConjunctiveGraph:
    """Return a new graph with blank nodes renamed according to mapping."""

    def _remap(node: rdflib.term.Node) -> rdflib.term.Node:
        if isinstance(node, rdflib.BNode):
            new_label = mapping.get(str(node), str(node))
            return rdflib.BNode(new_label)
        return node

    new_g = rdflib.ConjunctiveGraph()
    for s, p, o in g:
        new_g.add((_remap(s), p, _remap(o)))  # type: ignore[arg-type]
    return new_g


def _shuffle_graph(
    g: rdflib.ConjunctiveGraph,
    rng: random.Random,
) -> rdflib.ConjunctiveGraph:
    """Return a new graph with the same triples inserted in shuffled order."""
    triples = list(g)
    rng.shuffle(triples)
    new_g = rdflib.ConjunctiveGraph()
    for s, p, o in triples:
        new_g.add((s, p, o))
    return new_g


# ---------------------------------------------------------------------------
# Property tests
# ---------------------------------------------------------------------------


@given(graph=_graph_st())
@settings(max_examples=200)
def test_blank_node_relabeling_invariance(graph: rdflib.ConjunctiveGraph) -> None:
    """Renaming blank nodes via any bijection must not change the canonical output."""
    bnodes = [str(n) for n in graph.all_nodes() if isinstance(n, rdflib.BNode)]
    if not bnodes:
        return  # vacuously true; no blank nodes to relabel

    # Build a random bijection: shuffle the labels and map each to the next
    shuffled = bnodes[:]
    random.shuffle(shuffled)
    mapping = dict(zip(bnodes, shuffled, strict=False))

    relabeled = _relabel(graph, mapping)
    assert canonicalize(graph) == canonicalize(relabeled)


@given(graph=_graph_st())
@settings(max_examples=200)
def test_quad_order_invariance(graph: rdflib.ConjunctiveGraph) -> None:
    """Inserting triples in a different order must not change the canonical output."""
    shuffled = _shuffle_graph(graph, random.Random(42))  # noqa: S311
    assert canonicalize(graph) == canonicalize(shuffled)


@given(graph=_graph_st())
@settings(max_examples=100)
def test_idempotency(graph: rdflib.ConjunctiveGraph) -> None:
    """Canonicalizing the canonical output again must yield the same string."""
    first = canonicalize(graph)
    # Parse the canonical N-Quads back into a fresh graph and re-canonicalize
    second_graph = rdflib.ConjunctiveGraph()
    second_graph.parse(data=first, format="nquads")
    second = canonicalize(second_graph)
    assert first == second
