# Notes for AI agents

Read [README.md](README.md) for how this repository works (black-box `Api`s, `Contracts`, checks
recorded in `checks.toml`, theorems proved from them) and [STYLE.md](STYLE.md) before changing any
Lean file. Follow STYLE.md: in particular, no `sorry` or `axiom`, minimal contracts, and Rust paths
at the start of every `Api` doc.

## Keep the READMEs in sync

Each folder under `FastcryptoSpecs/` has a `README.md` with a table of its files, and tables of its
theorems and contracts with a one-line summary each and how each contract was checked
(`Avss/README.md` is the model; add the tables to a folder that lacks them when you next touch it).
In the same change as any of the following, update that folder's README:

- adding, removing, renaming or changing the statement of a theorem, contract or assumption
  structure;
- adding or removing a file;
- checking a contract (also update its entry in `checks.toml`: revision, method, date, and `pr` if
  the revision is not on fastcrypto's main yet).

Update the top-level `README.md` if how the repository works changes, e.g. a new check method.
READMEs describe the current state only; what changed goes in the commit message or PR.

## Before you finish

```bash
lake build
python3 scripts/check_contracts.py
```

Both run in CI. The build must succeed with no `sorry` warnings, and the script must report no
missing or extra `checks.toml` entries.
