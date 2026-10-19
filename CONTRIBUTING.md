# Contributing

## Prerequisites

- [Python 3.11+](https://www.python.org/)
- [Poetry](https://python-poetry.org/) — `pip install poetry`
- [Task](https://taskfile.dev/) — `brew install go-task` (macOS) or see [installation docs](https://taskfile.dev/installation/)
- [poetry-dynamic-versioning](https://github.com/mtkennerly/poetry-dynamic-versioning) plugin — `poetry self add "poetry-dynamic-versioning[plugin]"`

## Setup

```bash
git clone <repo>
cd rdf-canonicalization
poetry install
```

## Development tasks

Run `task` to see all available tasks.  The most common ones:

| Command | What it does |
|---|---|
| `task check` | Run the full suite: linters + tests |
| `task check:pytest` | Tests only (pytest + coverage) |
| `task check:linters` | ruff + mypy + safety |
| `task check:ruff` | Format check and lint |
| `task check:mypy` | Type checking |
| `task format:fix` | Auto-format and fix lint issues |

Run the test suite directly with pytest:

```bash
poetry run pytest tests/
```

## Code style

This project uses [ruff](https://docs.astral.sh/ruff/) for formatting and linting
(`select = ["ALL"]` with a small ignore list in `pyproject.toml`) and
[mypy](https://mypy-lang.org/) for type checking.  All checks must pass before
a PR is merged.

```bash
poetry run ruff format tests graph_sign_and_verify_c4gai
poetry run ruff check  tests graph_sign_and_verify_c4gai
poetry run mypy -p tests -p graph_sign_and_verify_c4gai
```

## Changelog

Follow [Keep a Changelog](https://keepachangelog.com/) format.  Add an entry
under `[Unreleased]` for every user-visible change.

## Versioning

Releases follow [Semantic Versioning](https://semver.org/).  The version is
derived from git tags by `poetry-dynamic-versioning`; do not edit
`pyproject.toml`'s `version` field.

## Pull requests

- Keep changes focused — one concern per PR.
- Make sure `task check` passes locally before opening a PR.
- Reference any relevant issue in the PR description.
