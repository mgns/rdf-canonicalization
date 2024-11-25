import hashlib
from datetime import time, datetime, date

import rdflib
from collections import defaultdict
import itertools

from rdflib import Graph

from graph_sign_and_verify_c4gai.graphsignature import hash_rdf


class RdfNormalize:
    def __init__(self, graph, max_run_time=None):
        """
        Initialize the RDF normalization process.
        :param graph: an instance of rdflib.Graph containing the RDF data.
        :param max_run_time: optional maximum runtime in seconds for the normalization process.
        @type graph: object
        """
        self.graph = graph
        self.max_run_time = max_run_time
        self.blank_id_to_quad_set = defaultdict(set)
        self.canon_issuer = IdentifierIssuer()
        self.hash_to_blank_id = defaultdict(set)
        self.non_normalized = set()
        self.start_time = None

    @property
    def normalize(self):
        """
        Main method to normalize the RDF graph using a deterministic algorithm.
        """
        self.start_time = datetime.now()
        self.collect_blank_nodes()
        self.issue_canonical_ids()
        return self.serialize_normalized_graph()

    def collect_blank_nodes(self):
        """
        Collect blank nodes and map them to the triples (quads) that reference them.
        """
        for s, p, o in self.graph:
            if isinstance(s, rdflib.BNode):
                self.blank_id_to_quad_set[s].add((s, p, o))
                self.non_normalized.add(s)
            if isinstance(o, rdflib.BNode):
                self.blank_id_to_quad_set[o].add((s, p, o))
                self.non_normalized.add(o)

    def issue_canonical_ids(self):
        """
        Assign deterministic IDs to blank nodes.
        """
        simple = True
        while simple:
            self.check_runtime()
            simple = False
            self.hash_to_blank_id.clear()

            for blank_id in self.non_normalized:
                hash_value = self.hash_first_degree(blank_id)
                self.hash_to_blank_id[hash_value].add(blank_id)

            for hash_value, blank_ids in list(self.hash_to_blank_id.items()):
                if len(blank_ids) == 1:
                    single_blank = next(iter(blank_ids))
                    self.canon_issuer.get_id(single_blank)
                    self.non_normalized.remove(single_blank)
                    del self.hash_to_blank_id[hash_value]
                    simple = True

    def hash_first_degree(self, blank_id):
        """
        Compute the first-degree hash for a blank node based on its adjacent triples.
        :param blank_id: a blank node (BNode instance).
        :return: a string representing the SHA-256 hash.
        """
        quads = self.blank_id_to_quad_set[blank_id]
        serialized_quads = sorted(self.serialize_quad(q, blank_id) for q in quads)
        serialized_data = ''.join(serialized_quads).encode('utf-8')
        return hashlib.sha256(serialized_data).hexdigest()

    def serialize_quad(self, quad, blank_id):
        """
        Serialize a quad into a deterministic string format.
        Replace the blank node with a placeholder.
        :param quad: a triple (s, p, o).
        :param blank_id: the blank node being hashed.
        :return: a string serialization of the quad.
        """
        def term_to_string(term):
            if term == blank_id:
                return '_:a'  # Placeholder for the blank node being hashed
            elif isinstance(term, rdflib.BNode):
                return '_:b'
            elif isinstance(term, rdflib.URIRef):
                return f"<{term}>"
            elif isinstance(term, rdflib.Literal):
                return f"\"{term}\""
            return str(term)

        return f"{term_to_string(quad[0])} {term_to_string(quad[1])} {term_to_string(quad[2])} ."

    def serialize_normalized_graph(self):
        """
        Serialize the normalized graph into a canonical format (N-Quads or similar).
        :return: the normalized graph as a string.
        """
        normalized_graph = rdflib.Graph()
        for s, p, o in self.graph:
            s = self.replace_blank_with_canonical(s)
            o = self.replace_blank_with_canonical(o)
            normalized_graph.add((s, p, o))
        return normalized_graph.serialize(format='nt')  # Return as N-Triples for simplicity

    def replace_blank_with_canonical(self, term):
        """
        Replace a blank node with its canonical identifier.
        :param term: a term in the graph.
        :return: the term with blank nodes replaced by canonical IDs.
        """
        if isinstance(term, rdflib.BNode) and term in self.canon_issuer.ids:
            return rdflib.BNode(self.canon_issuer.ids[term])
        return term

    def runtime(self):
        datetime.now() - self.start_time

    def check_runtime(self):
        """
        Check if the maximum runtime has been exceeded.
        """
#        if self.max_run_time and (self.runtime() > self.max_run_time):
#            raise TimeoutError("Normalization process exceeded the maximum runtime.")

class IdentifierIssuer:
    """
    A class to manage deterministic issuance of identifiers for blank nodes.
    """
    def __init__(self):
        self.ids = {}
        self.counter = itertools.count()

    def get_id(self, blank_node):
        """
        Get or assign a deterministic ID for the given blank node.
        :param blank_node: a BNode.
        :return: the deterministic identifier.
        """
        if blank_node not in self.ids:
            self.ids[blank_node] = f"b{next(self.counter)}"
        return self.ids[blank_node]


# Example Usage
if __name__ == "__main__":
    file = "order-1.nt"

    graph: Graph = rdflib.Graph()
    graph.parse(file, format="turtle")  # Replace with your RDF file path

    normalizer = RdfNormalize(graph, max_run_time=5)
    normalized_output = sorted(normalizer.normalize.splitlines())
    print("\n".join(normalized_output))

    # Hash the canonical graph
    rdf_hash = hash_rdf("\n".join(normalized_output))
    print("Hash:", rdf_hash.hex())
    with open(file + ".sha", "a") as f:
        f.write(rdf_hash.hex())
        f.write(" rdf_normalizer\n")