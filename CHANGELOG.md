# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/) and this project adheres to [Semantic Versioning](https://semver.org/)

## [Unreleased]

### Added

- Full RDFC 1.0 (W3C Recommendation 2024) canonicalization — passes all 86
  W3C manifest tests (64 eval, 21 map, 1 negative) with zero failures
- SHA-384 hash algorithm support alongside the default SHA-256
- Manifest-driven W3C test suite (`tests/test_canonicalization.py`) with
  parametrized eval, map, and negative/poison test types
- Hypothesis property tests: blank-node relabeling and quad-order invariance,
  plus idempotency
- `canonicalize()` public API accepting rdflib `ConjunctiveGraph`/`Graph` or
  raw N-Quads text; returns sorted canonical N-Quads string
- `RdfCanonicalization` class exposing the issued blank-node ID map
  (`canon_issuer.ids`) for map-test verification
- `max_run_time` (wall-clock) and `max_work_factor` (deterministic,
  machine-independent) poison-graph limits; both raise `TimeoutError`
- `canonicalize` CLI: reads FILE or stdin, supports `--format`,
  `--hash-algorithm`, `--max-run-time`, `--max-work-factor`
- `graphsign` CLI with four subcommands: `keygen`, `hash`, `sign`, `verify`

### Changed

- Rewrote RDFC 1.0 algorithm to match the spec exactly:
  - HashFirstDegreeQuads: correct `_:a`/`_:z` substitution and `\n` termination
  - Main loop: single-pass first-degree hashing, singleton ID issuance
  - HashRelatedBlankNode: correct `<predicate>` wrapping; no predicate for `g`
  - HashNDegreeQuads: correct path format, recursion `<hash>` suffix,
    first-degree-hash-group ordering
  - Literals: full N-Quads escape set (`\b \t \f \uXXXX`); `xsd:string` dropped
  - Serializer: own implementation — sorted, `\n`-terminated, no rdflib round-trip
- `graphsignature.py` rewritten: removed misleading `canonicalize_rdf` and
  broken `find_blank_nodes`; `hash_rdf` now takes a `Graph` and uses the real
  canonicalizer; `verify_signature` catches `InvalidSignature` specifically
- Fixed signing double-hash: `sign_hash` now uses `Prehashed(SHA256())` so
  the signed value is `SHA-256(canonical)` rather than `SHA-256(SHA-256(canonical))`
- Performance: pre-bound hash constructor, single-element permutation fast path,
  single-lookup dict access in hot paths, sampled wall-clock timer

### Removed

- `sign.py` (ran file I/O at import)
- Committed artefacts: `tmp/*.nt`, `order-1.nt.sha`, root `order-1.nt`
- Template stubs: `example.py`, `test_example.py`
- Misleading module-level globals in `graphsignature.py`
