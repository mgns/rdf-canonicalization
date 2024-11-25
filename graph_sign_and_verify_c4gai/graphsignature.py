from datetime import time, datetime, date
from typing import List, LiteralString

from rdflib import Graph, BNode
import hashlib
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.primitives import serialization



blank_id = {}
non_normalized = set()  # Set of non-normalized RdfValue objects

max_run_time = 1000  # Example max run time in milliseconds (set appropriately)
start_time = time()  # Used to track the runtime


# Step 1: Canonicalize the RDF Graph
def canonicalize_rdf(graph: Graph):
    # Search for blanks
    find_blank_nodes(graph)

    # Serialize the graph to N-Triples
    serialized_graph = graph.serialize(format="nt")
    # Sort the triples for consistent ordering
    sorted_triples = sorted(serialized_graph.splitlines())
    # Join sorted triples back into a single string
    return "\n".join(sorted_triples)

def find_blank_nodes(graph: Graph):
    for s, p, o in graph.triples((None, None, None)):
        if type(s) == BNode:
            bgraph = blank_id.setdefault(s, Graph())
            bgraph.add((s, p, o))
        if type(o) == BNode:
            bgraph = blank_id.setdefault(s, Graph())
            bgraph.add((s, p, o))

    for bg in blank_id:
        print(bg)

# Step 2: Hash the Canonicalized RDF Graph
def hash_rdf(canonicalized_graph: str):
    return hashlib.sha256(canonicalized_graph.encode('utf-8')).digest()

# Step 3: Generate a Key Pair
def generate_key_pair():
    private_key = rsa.generate_private_key(
        public_exponent=65537,
        key_size=2048,
    )
    public_key = private_key.public_key()
    return private_key, public_key

# Step 4: Sign the Hash
def sign_hash(private_key, rdf_hash):
    signature = private_key.sign(
        rdf_hash,
        padding.PSS(
            mgf=padding.MGF1(hashes.SHA256()),
            salt_length=padding.PSS.MAX_LENGTH,
        ),
        hashes.SHA256(),
    )
    return signature

# Step 5: Verify the Signature
def verify_signature(public_key, rdf_hash, signature):
    try:
        public_key.verify(
            signature,
            rdf_hash,
            padding.PSS(
                mgf=padding.MGF1(hashes.SHA256()),
                salt_length=padding.PSS.MAX_LENGTH,
            ),
            hashes.SHA256(),
        )
        return True
    except Exception as e:
        return False

# Example Usage
if __name__ == "__main__":
    file = "order-1.nt"

    # Create an RDF graph
    g = Graph()
    g.parse(file)

    # Canonicalize the graph
    canonical_graph = canonicalize_rdf(g)
    # canonicalize_rdf(g)
    print("Canonical Graph:\n", canonical_graph)

    # Hash the canonical graph
    rdf_hash = hash_rdf(canonical_graph)
    print("Hash:", rdf_hash.hex())
    with open(file + ".sha", "a") as f:
        f.write(rdf_hash.hex())
        f.write(" canonicalize_rdf\n")

    # Generate keys
    private_key, public_key = generate_key_pair()

    # Sign the hash
    signature = sign_hash(private_key, rdf_hash)
    print("Signature:", signature.hex())

    # Verify the signature
    is_valid = verify_signature(public_key, rdf_hash, signature)
    print("Signature valid:", is_valid)

    # Export public key (optional for external verification)
    public_key_pem = public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo,
    )
    print("Public Key (PEM):\n", public_key_pem.decode("utf-8"))

    exit = time()
    duration = datetime.combine(date.today(), exit) - datetime.combine(date.today(), start_time)
    print("Time:\n", duration)
