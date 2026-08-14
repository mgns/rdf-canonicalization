# graph-sign-and-verify-c4gai

Sign and verify your awesome Knowledge Graphs with eccenca Corporate Memory :-)

[![workflow](https://github.com/eccenca/rdf-canonicalization/actions/workflows/check.yml/badge.svg)](https://github.com/eccenca/rdf-canonicalization/actions) [![pypi version](https://img.shields.io/pypi/v/graph-sign-and-verify-c4gai)](https://pypi.org/project/graph-sign-and-verify-c4gai) [![license](https://img.shields.io/pypi/l/graph-sign-and-verify-c4gai)](https://pypi.org/project/graph-sign-and-verify-c4gai)
[![poetry][poetry-shield]][poetry-link] [![ruff][ruff-shield]][ruff-link] [![mypy][mypy-shield]][mypy-link] [![copier][copier-shield]][copier] 

## Usage

### RDF Canonicalization (RDFC-1.0)

`RdfCanonicalization` implements the [RDFC-1.0](https://www.w3.org/TR/rdf-canon/) dataset normalization algorithm, producing a canonical N-Triples string with deterministic blank node identifiers.

```python
import rdflib
from graph_sign_and_verify_c4gai.rdf_canonicalization import RdfCanonicalization

graph = rdflib.Graph()
graph.parse("my_graph.ttl", format="turtle")

normalizer = RdfCanonicalization(graph, max_run_time=5)
canonical = normalizer.normalize  # sorted, deterministic N-Triples string
print(canonical)
```

- `max_run_time` (optional): maximum seconds allowed before a `TimeoutError` is raised.
- The `normalize` property runs the full pipeline and returns the canonical N-Triples string.

### Graph Signing and Verification

`graphsignature` provides a simpler canonicalization (sorted N-Triples) combined with RSA-PSS signing and verification.

```python
from rdflib import Graph
from graph_sign_and_verify_c4gai.graphsignature import (
    canonicalize_rdf,
    hash_rdf,
    generate_key_pair,
    sign_hash,
    verify_signature,
)

# Load an RDF graph
graph = Graph()
graph.parse("my_graph.nt")

# Canonicalize and hash
canonical = canonicalize_rdf(graph)
rdf_hash = hash_rdf(canonical)

# Generate an RSA-2048 key pair
private_key, public_key = generate_key_pair()

# Sign
signature = sign_hash(private_key, rdf_hash)

# Verify
is_valid = verify_signature(public_key, rdf_hash, signature)
print("Signature valid:", is_valid)
```

## Development

- Run [task](https://taskfile.dev/) to see all major development tasks.
- Use [pre-commit](https://pre-commit.com/) to avoid errors before commit.
- This repository was created with [this copier template](https://github.com/eccenca/cmem-plugin-template).


[poetry-link]: https://python-poetry.org/
[poetry-shield]: https://img.shields.io/endpoint?url=https://python-poetry.org/badge/v0.json
[ruff-link]: https://docs.astral.sh/ruff/
[ruff-shield]: https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/astral-sh/ruff/main/assets/badge/v2.json&label=Code%20Style
[mypy-link]: https://mypy-lang.org/
[mypy-shield]: https://www.mypy-lang.org/static/mypy_badge.svg
[copier]: https://copier.readthedocs.io/
[copier-shield]: https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/copier-org/copier/master/img/badge/badge-grayscale-inverted-border-purple.json
