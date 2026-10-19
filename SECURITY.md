# Security Policy

## Reporting a Vulnerability

Please **do not** open a public GitHub issue for security vulnerabilities.

Report security issues by email to **532480+mgns@users.noreply.github.com**.  Include a
description of the issue, the affected version, and steps to reproduce it.
You can expect an acknowledgement within 5 business days.

## Supported Versions

Only the latest release receives security fixes.

## Scope

This library implements:

- **RDFC 1.0** (W3C Recommendation 2024) RDF dataset canonicalization
- **RSA-PSS/SHA-256** graph signing and verification

Security issues relevant to this library include:

- Incorrect canonicalization output that would cause two distinct graphs to
  produce the same canonical form (collision)
- Signing or verification logic errors that allow an invalid signature to be
  accepted as valid
- Denial-of-service via maliciously crafted RDF input (poison graphs — see
  below)

## Known Limitations

### Poison-graph protection is opt-in

Adversarial RDF graphs containing many blank nodes with identical
first-degree neighbourhood hashes can cause the RDFC 1.0 algorithm to
explore a factorial number of blank-node permutations.  This library
provides two independent limits:

| Parameter | Default | Effect |
|---|---|---|
| `max_run_time` | `None` (off) | Wall-clock timeout in seconds |
| `max_work_factor` | `None` (off) | `N × blank_node_count` permutation steps |

Both raise `TimeoutError` when exceeded.  **Applications that process
untrusted RDF input should enable at least one limit.**  Example:

```python
canonicalize(graph, max_work_factor=4096, max_run_time=30.0)
```

The CLI exposes the same flags (`--max-work-factor` / `--max-run-time`).

### Global rdflib state

Importing this library sets `rdflib.NORMALIZE_LITERALS = False` at module
load time.  This is required for spec-correct literal serialization (RDFC 1.0
§4.5) but affects all rdflib usage in the same Python process.  If your
application relies on rdflib's default literal normalization behaviour for
other purposes, be aware of this side effect.

### Private key storage

`graphsign keygen` writes the private key as an unencrypted PEM file
(`NoEncryption()`).  Protect the file with appropriate filesystem permissions
(e.g. `chmod 600 private.pem`).  Key encryption at rest is the caller's
responsibility.

### RSA key size

Keys are RSA-2048.  This meets NIST recommendations through 2030.  If your
security policy requires stronger keys, this library does not currently
support larger key sizes or alternative algorithms (e.g. ECDSA).

### `verify_signature` return value

`verify_signature()` returns `bool` rather than raising on failure.  Callers
must check the return value; ignoring it silently accepts an invalid
signature.
