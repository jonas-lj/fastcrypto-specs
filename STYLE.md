# Style

How specifications in this repository are written. The goal is that a reviewer, human or LLM, can
read off exactly what is assumed and what is proved, without reading proofs.

## Scope

The specs assume that every contract holds. Whether the Rust code satisfies its contracts, or a
caller such as Hashi meets its obligations, is checked elsewhere (tests, model checking, review)
and is not recorded here.

## Structure

1. One file per building block, in this order: `Api` (the Rust functions as black boxes),
   `Contracts` (what we expect from them), the execution and caller model, then theorems.
2. Every assumption is a field of a named structure: a contract (`Contracts`, `DkgContracts`), a
   caller obligation or network assumption (`Run`, `Certificate`, ...), or the parameters
   (`Setup.Valid`). A condition used in several theorems gets a named definition
   (e.g. `Setup.Tolerates`).
3. Theorems are proved from their hypotheses only: no `axiom`, `sorry` or assumptions in
   `variable` declarations.

## Naming

4. `Api` fields are the Rust function names in camelCase. Their docs give the Rust call they stand
   for (e.g. `` `Receiver::process_message(message)`, run by receiver `i`. ``).
5. Contract and assumption fields are named after what they state (`recover_sound`,
   `process_invalid_iff`, `gets_message`), not numbered.

## Docs

6. Documentation lives on the Lean declaration it describes, never in a separate file.
7. A contract's doc is its statement as a short formula over the Rust calls, e.g.
   `` `recover_i(m, vs) = Ok(o)` ⇒ `verify_i(m, o.my_shares)` ``. Notation such as `f_i` is defined
   once, in the doc of the enclosing structure.
8. An assumption's doc says what it states and, for non-contracts, whether it is a caller obligation
   or a network assumption. It does not say which theorems use it, why it holds, or how it is
   checked.
9. An idealization (no panics, determinism, shared configuration, abstracted randomness) is stated
   once, on the declaration it applies to (usually `Api`).
10. A theorem's doc states the conclusion in Rust terms. It does not restate hypotheses that are
    named structures or definitions; the reviewer reads those where they are defined. Only
    hypotheses written out in the signature (e.g. "`dealers` is nonempty") are mentioned.

## Contracts

11. Contracts only relate the black-box functions to each other; no algebra. A new concept becomes
    a new black box (as `DkgApi` did), not a Lean definition of its implementation.
12. A contract states no more than the proofs need. Weaker contracts are easier to check and
    survive refactors of the Rust code.

## Proofs

13. Proofs are short and split into lemmas, one per step. Prefer `obtain`, `rw` and `exact` to
    large `simp` calls, so that proofs survive Mathlib upgrades and are easy to repair.
14. Each model has a non-vacuity check: a concrete instance satisfying its contracts and
    execution assumptions, so that the assumptions are known to be consistent.
