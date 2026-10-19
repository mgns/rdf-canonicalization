"""RDF dataset canonicalization (RDFC 1.0) and RSA-PSS graph signing."""

from importlib.metadata import PackageNotFoundError, version

from graph_sign_and_verify_c4gai.graphsignature import (
    generate_key_pair,
    hash_rdf,
    sign_hash,
    verify_signature,
)
from graph_sign_and_verify_c4gai.rdf_canonicalization import RdfCanonicalization, canonicalize

try:
    __version__ = version("graph-sign-and-verify-c4gai")
except PackageNotFoundError:
    __version__ = "unknown"

__all__ = [
    "RdfCanonicalization",
    "canonicalize",
    "generate_key_pair",
    "hash_rdf",
    "sign_hash",
    "verify_signature",
]
