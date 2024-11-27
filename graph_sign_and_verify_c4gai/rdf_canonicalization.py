import hashlib
import timeit

import rdflib
from collections import defaultdict
import itertools

from rdflib import Graph

from graph_sign_and_verify_c4gai.graphsignature import hash_rdf


class RdfCanonicalization:
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
        self.start_time = timeit.default_timer()
        self.collect_blank_nodes()
        self.issue_canonical_ids() # normalization for simple nodes
        self.issue_n_degree_ids()  # N-degree normalization for remaining nodes
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

    def issue_n_degree_ids(self):
        """
        Assign deterministic IDs to blank nodes based on n-degree hash computation.
        """
        permutation_limit = 1_000_000  # Example limit on permutations
        while self.non_normalized:
            self.check_runtime()
            hash_to_related_blank_ids = defaultdict(set)

            # Compute n-degree hash for all non-normalized blank nodes
            for blank_id in self.non_normalized:
                hash_value = self.hash_n_degree(blank_id)
                hash_to_related_blank_ids[hash_value].add(blank_id)

            # Sort hash values for deterministic processing
            sorted_hashes = sorted(hash_to_related_blank_ids.keys())

            for hash_value in sorted_hashes:
                blank_ids = hash_to_related_blank_ids[hash_value]

                if len(blank_ids) > permutation_limit:
                    raise ValueError(f"Exceeded the permutation limit for hash {hash_value}")

                # Process each permutation of blank nodes deterministically
                for permutation in itertools.permutations(blank_ids):
                    self.check_runtime()

                    issuer = IdentifierIssuer()  # Temporary issuer for this round
                    for blank_id in permutation:
                        issuer.get_id(blank_id)

                    # Compute the canonical hash for this permutation
                    canonical_hash = self.compute_canonical_hash(permutation, issuer)

                    # Assign canonical IDs if this hash is unique
                    if canonical_hash not in self.canon_issuer.ids:
                        for blank_id in permutation:
                            self.canon_issuer.get_id(blank_id)
                        self.non_normalized -= set(permutation)  # Remove processed nodes
                        break  # Stop processing this hash group
        return

    def hash_n_degree(self, blank_id):
        """
        Compute an n-degree hash for a blank node by considering its connected triples recursively.
        :param blank_id: the blank node to hash.
        :return: the computed hash as a string.
        """
        temp_issuer = IdentifierIssuer()
        stack = [(blank_id, None)]
        visited = set()
        serialized_components = []

        while stack:
            current_node, parent_triple = stack.pop()
            if current_node in visited:
                continue
            visited.add(current_node)

            if isinstance(current_node, rdflib.BNode):
                identifier = temp_issuer.get_id(current_node)
            else:
                identifier = str(current_node)

            if parent_triple:
                serialized_components.append(self.serialize_quad(parent_triple, blank_id))
            serialized_components.append(identifier)

            for triple in self.graph.triples((current_node, None, None)):
                stack.append((triple[2], triple))
            for triple in self.graph.triples((None, None, current_node)):
                stack.append((triple[0], triple))

        serialized_data = '\n'.join(sorted(serialized_components)).encode('utf-8')
        return hashlib.sha256(serialized_data).hexdigest()

    def compute_canonical_hash(self, permutation, temp_issuer):
        """
        Compute a canonical hash for a given permutation of blank nodes.
        :param permutation: a list of blank nodes in a specific order.
        :param temp_issuer: a temporary IdentifierIssuer instance for the current permutation.
        :return: the canonical hash as a string.
        """
        serialized_components = []

        for blank_id in permutation:
            temp_id = temp_issuer.get_id(blank_id)
            quads = self.blank_id_to_quad_set[blank_id]
            for quad in quads:
                serialized_components.append(self.serialize_quad(quad, blank_id).replace('_:a', temp_id))

        serialized_data = ''.join(sorted(serialized_components)).encode('utf-8')
        return hashlib.sha256(serialized_data).hexdigest()

    def hash_first_degree(self, blank_id):
        """
        Compute the first-degree hash for a blank node based on its adjacent triples.
        :param blank_id: a blank node (BNode instance).
        :return: a string representing the SHA-256 hash.
        """
        quads = self.blank_id_to_quad_set[blank_id]
        serialized_quads = sorted(self.serialize_quad(q, blank_id) for q in quads)
        serialized_data = '\n'.join(serialized_quads).encode('utf-8')
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
        return timeit.default_timer() - self.start_time

    def check_runtime(self):
        """
        Check if the maximum runtime has been exceeded.
        """
        if self.max_run_time and (self.runtime() > self.max_run_time):
            raise TimeoutError("Normalization process exceeded the maximum runtime.")

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
            self.ids[blank_node] = f"c14n{next(self.counter)}"
        return self.ids[blank_node]


# Example Usage
if __name__ == "__main__":
    #file = "order-1.nt"
    file = "../tests/rdfc10/test023-in.nq"

    graph: Graph = rdflib.Graph()
    graph.parse(file, format="turtle")  # Replace with your RDF file path

    normalizer = RdfCanonicalization(graph, max_run_time=5)
    normalized_output = sorted(normalizer.normalize.splitlines())
    print("\n".join(normalized_output))

    # Hash the canonical graph
    rdf_hash = hash_rdf('\n'.join(normalized_output))
    print("Hash:", rdf_hash.hex())
    with open(file + ".sha", "a") as f:
        f.write(rdf_hash.hex())
        f.write(" rdf_normalizer\n")
