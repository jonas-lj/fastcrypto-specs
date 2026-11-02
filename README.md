# fastcrypto-specs

Lean specifications and proofs for fastcrypto building blocks. They serve two purposes:

- **A review tool.** Every assumption is stated precisely, and the protocol reasoning built on them
  is checked by Lean.
- **Documentation.** The obligations on callers and the assumptions about the code and the network
  are written down in one place, and CI checks that the theorems still follow from them.

## Approach

We do not translate Rust into Lean. For each building block:

1. **Black boxes.** The Rust functions appear in Lean with the same names and inputs/outputs,
   but without implementations.
2. **Contracts.** We state in Lean what we expect from them, only by relating the functions to
   each other (e.g. "`recover_c0` returns `c0` of a polynomial from `t` of its shares").
3. **Checks.** Each contract is checked against the Rust code: unit/property tests, review
   (LLM-assisted or not), or a model checker such as Kani. The fastcrypto revision each contract
   was last checked against is recorded in the folder's `checks.toml`, outside the Lean files.
4. **Theorems.** We prove properties of how the building blocks compose, from the contracts and
   from explicit assumptions about the caller and the environment (e.g. the network).

The theorems hold for any implementation that satisfies the contracts, so nothing depends on a
faithful translation. The trust boundary is the set of hypotheses of each theorem: function
contracts, caller obligations and environment assumptions. Each one is documented on its Lean
declaration.

The specs are kept minimal so that they stay maintainable as they grow: something is added only if
it gives an assurance that tests and human review cannot give easily, such as a protocol property
over all executions, a property of a distribution, or a result about how several building blocks
compose. See [STYLE.md](STYLE.md) for what belongs here and how the specs are written.

What this does not give: a proof that the Rust code satisfies its contracts, or that the caller
meets its obligations. That rests on the checks in step 3.

## Build

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

CI (`.github/workflows/ci.yml`) runs the same build on every push and pull request, and
`scripts/check_contracts.py`, which checks that every contract has an entry in its folder's
`checks.toml` and warns about contracts that have not been checked yet.
