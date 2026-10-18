"""RDF graph signing and verification utilities."""

import argparse
import hashlib
import sys
from pathlib import Path

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding, rsa, utils
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPrivateKey, RSAPublicKey
from cryptography.hazmat.primitives.serialization import (
    Encoding,
    NoEncryption,
    PrivateFormat,
    PublicFormat,
    load_pem_private_key,
    load_pem_public_key,
)
from rdflib import Graph

from graph_sign_and_verify_c4gai.rdf_canonicalization import canonicalize

_RSA_EXPONENT = 65537
_RSA_KEY_SIZE = 2048


def hash_rdf(graph: Graph) -> bytes:
    """Return SHA-256 digest of the RDFC 1.0 canonical N-Quads of graph."""
    canonical = canonicalize(graph)
    return hashlib.sha256(canonical.encode("utf-8")).digest()


def generate_key_pair() -> tuple[RSAPrivateKey, RSAPublicKey]:
    """Generate a fresh 2048-bit RSA key pair."""
    private_key = rsa.generate_private_key(
        public_exponent=_RSA_EXPONENT,
        key_size=_RSA_KEY_SIZE,
    )
    return private_key, private_key.public_key()


def sign_hash(private_key: RSAPrivateKey, rdf_hash: bytes) -> bytes:
    """Sign rdf_hash with private_key using RSA-PSS/SHA-256.

    rdf_hash must be a raw SHA-256 digest (32 bytes).  Prehashed tells PSS
    not to hash it again, so the signed value is exactly rdf_hash.
    """
    return private_key.sign(
        rdf_hash,
        padding.PSS(
            mgf=padding.MGF1(hashes.SHA256()),
            salt_length=padding.PSS.MAX_LENGTH,
        ),
        utils.Prehashed(hashes.SHA256()),
    )


def verify_signature(
    public_key: RSAPublicKey,
    rdf_hash: bytes,
    signature: bytes,
) -> bool:
    """Return True if signature is a valid RSA-PSS/SHA-256 signature over rdf_hash."""
    try:
        public_key.verify(
            signature,
            rdf_hash,
            padding.PSS(
                mgf=padding.MGF1(hashes.SHA256()),
                salt_length=padding.PSS.MAX_LENGTH,
            ),
            utils.Prehashed(hashes.SHA256()),
        )
    except InvalidSignature:
        return False
    else:
        return True


def _load_graph(input_path: str | None, fmt: str) -> Graph:
    """Parse an RDF file (or stdin) into a ConjunctiveGraph."""
    from rdflib import ConjunctiveGraph  # local to avoid a top-level cycle risk

    g = ConjunctiveGraph()
    if input_path is None or input_path == "-":
        g.parse(data=sys.stdin.read(), format=fmt)
    else:
        g.parse(input_path, format=fmt)
    return g


def main() -> None:
    """Sign and verify RDF datasets using RSA-PSS over RDFC 1.0 canonical hashes.

    Subcommands:
      keygen  Generate an RSA-2048 key pair.
      hash    Print the hex SHA-256 hash of the canonical form.
      sign    Sign a graph and write the binary signature.
      verify  Verify a signature against a graph.
    """
    parser = argparse.ArgumentParser(
        prog="graphsign",
        description="Sign and verify RDF datasets (RSA-PSS/SHA-256 over RDFC 1.0)",
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    # keygen
    kg = sub.add_parser("keygen", help="generate an RSA-2048 key pair")
    kg.add_argument(
        "--out-private",
        default="private.pem",
        metavar="FILE",
        help="private key PEM output (default: private.pem)",
    )
    kg.add_argument(
        "--out-public",
        default="public.pem",
        metavar="FILE",
        help="public key PEM output (default: public.pem)",
    )

    # hash
    hp = sub.add_parser("hash", help="print canonical RDFC 1.0 hash of a graph")
    hp.add_argument("input", nargs="?", metavar="FILE", help="RDF input file or '-' for stdin")
    hp.add_argument("--format", "-f", default="nquads", dest="fmt", metavar="FORMAT")

    # sign
    sg = sub.add_parser("sign", help="sign a graph's canonical hash")
    sg.add_argument("input", nargs="?", metavar="FILE")
    sg.add_argument("--format", "-f", default="nquads", dest="fmt", metavar="FORMAT")
    sg.add_argument("--key", required=True, metavar="PRIVATE_KEY_PEM", help="PEM private key file")
    sg.add_argument(
        "--out",
        default="signature.bin",
        metavar="FILE",
        help="signature output file (default: signature.bin)",
    )

    # verify
    vf = sub.add_parser("verify", help="verify a signature against a graph")
    vf.add_argument("input", nargs="?", metavar="FILE")
    vf.add_argument("--format", "-f", default="nquads", dest="fmt", metavar="FORMAT")
    vf.add_argument("--key", required=True, metavar="PUBLIC_KEY_PEM", help="PEM public key file")
    vf.add_argument(
        "--sig", required=True, metavar="SIGNATURE_FILE", help="binary signature file to verify"
    )

    args = parser.parse_args()

    try:
        if args.cmd == "keygen":
            priv, pub = generate_key_pair()
            Path(args.out_private).write_bytes(
                priv.private_bytes(Encoding.PEM, PrivateFormat.TraditionalOpenSSL, NoEncryption()),
            )
            Path(args.out_public).write_bytes(
                pub.public_bytes(Encoding.PEM, PublicFormat.SubjectPublicKeyInfo),
            )
            sys.stdout.write(f"Keys written: {args.out_private}, {args.out_public}\n")

        elif args.cmd == "hash":
            g = _load_graph(getattr(args, "input", None), args.fmt)
            sys.stdout.write(hash_rdf(g).hex() + "\n")

        elif args.cmd == "sign":
            g = _load_graph(getattr(args, "input", None), args.fmt)
            priv_key = load_pem_private_key(Path(args.key).read_bytes(), password=None)
            if not isinstance(priv_key, RSAPrivateKey):
                sys.exit("graphsign sign: key must be an RSA private key")
            sig = sign_hash(priv_key, hash_rdf(g))
            Path(args.out).write_bytes(sig)
            sys.stdout.write(f"Signature written to {args.out}\n")

        elif args.cmd == "verify":
            g = _load_graph(getattr(args, "input", None), args.fmt)
            pub_key = load_pem_public_key(Path(args.key).read_bytes())
            if not isinstance(pub_key, RSAPublicKey):
                sys.exit("graphsign verify: key must be an RSA public key")
            sig = Path(args.sig).read_bytes()
            if verify_signature(pub_key, hash_rdf(g), sig):
                sys.stdout.write("Signature valid\n")
            else:
                sys.exit("graphsign verify: invalid signature")

    except Exception as exc:  # noqa: BLE001
        sys.exit(f"graphsign: error: {exc}")
