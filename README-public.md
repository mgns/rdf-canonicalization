# graph-sign-and-verify-c4gai

Sign and verify RDF Knowledge Graphs using
[RDFC 1.0](https://www.w3.org/TR/rdf-canon/) (W3C Recommendation 2024)
canonicalization and RSA-PSS signatures.

[![poetry][poetry-shield]][poetry-link] [![ruff][ruff-shield]][ruff-link] [![mypy][mypy-shield]][mypy-link]

## Conformance

The canonicalization engine passes all **86 entries** of the
[W3C RDFC 1.0 test suite](https://github.com/w3c/rdf-canon/tree/main/tests)
(64 eval, 21 map, 1 negative/poison), for both SHA-256 and SHA-384 hash
algorithms, with zero failures or expected failures.

## Installation

```bash
pip install graph-sign-and-verify-c4gai
```

Requires Python 3.11+.

## Python API

### Canonicalization

```python
from graph_sign_and_verify_c4gai.rdf_canonicalization import canonicalize
import rdflib

g = rdflib.ConjunctiveGraph()
g.parse("my-graph.nq", format="nquads")

# Returns a sorted N-Quads string (each line ends with \n)
canonical: str = canonicalize(g)

# SHA-384 variant
canonical_384: str = canonicalize(g, hash_algorithm="sha384")

# With poison-graph protection (see below)
canonical: str = canonicalize(g, max_run_time=10.0, max_work_factor=4096)
```

`canonicalize()` also accepts N-Quads text directly as `str` or `bytes`.

### Signing and verification

```python
from graph_sign_and_verify_c4gai.graphsignature import (
    generate_key_pair,
    hash_rdf,
    sign_hash,
    verify_signature,
)

private_key, public_key = generate_key_pair()

rdf_hash: bytes = hash_rdf(g)           # SHA-256 of canonical N-Quads
signature: bytes = sign_hash(private_key, rdf_hash)
valid: bool = verify_signature(public_key, rdf_hash, signature)
```

## Command-line tools

### `canonicalize`

```
canonicalize [FILE] [--format FORMAT] [--hash-algorithm ALGO]
             [--max-run-time SECONDS] [--max-work-factor N]
```

Reads FILE (or stdin when FILE is `-` or omitted), canonicalizes with
RDFC 1.0, and writes sorted N-Quads to stdout.

```bash
canonicalize graph.nq
canonicalize graph.ttl --format turtle
cat graph.nq | canonicalize --hash-algorithm sha384
```

### `graphsign`

```
graphsign keygen  [--out-private private.pem] [--out-public public.pem]
graphsign hash    [FILE] [--format FORMAT]
graphsign sign    [FILE] --key private.pem [--out signature.bin]
graphsign verify  [FILE] --key public.pem  --sig signature.bin
```

```bash
graphsign keygen
graphsign sign   graph.nq --key private.pem --out graph.sig
graphsign verify graph.nq --key public.pem  --sig graph.sig
```

All subcommands accept FILE or `-`/omitted for stdin.

## Poison-graph protection

Adversarial RDF graphs can cause the canonicalization algorithm to explore
a factorial number of blank-node permutations. Two independent limits are
available and can be combined:

| Parameter | Type | Behaviour |
|---|---|---|
| `max_run_time` | `float` (seconds) | Wall-clock timeout; raises `TimeoutError` |
| `max_work_factor` | `int` | Budget = `N × blank_node_count` permutation steps; raises `TimeoutError`; machine-independent |

The CLI exposes both as `--max-run-time` / `-t` and `--max-work-factor` / `-w`.

```bash
canonicalize poison.nq --max-work-factor 4096 --max-run-time 30
```

## Signing algorithm

Keys are RSA-2048. Signing uses RSA-PSS with SHA-256 (`MGF1(SHA-256)`,
`MAX_LENGTH` salt). The graph hash passed to `sign_hash` is treated as a
pre-computed SHA-256 digest (`Prehashed`), so the signed value is exactly
`SHA-256(canonical_N-Quads)`.


[poetry-link]: https://python-poetry.org/
[poetry-shield]: https://img.shields.io/endpoint?url=https://python-poetry.org/badge/v0.json
[ruff-link]: https://docs.astral.sh/ruff/
[ruff-shield]: https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/astral-sh/ruff/main/assets/badge/v2.json&label=Code%20Style
[mypy-link]: https://mypy-lang.org/
[mypy-shield]: https://www.mypy-lang.org/static/mypy_badge.svg
