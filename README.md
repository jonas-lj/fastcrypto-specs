# fastcrypto-specs

Lean specifications and proofs for fastcrypto building blocks.

## Approach

We do not translate Rust into Lean. For each building block:

1. **Black boxes.** The Rust functions appear in Lean with the same names and inputs/outputs,
   but without implementations.
2. **Contracts.** We state in Lean what we expect from them, only by relating the functions to
   each other (e.g. "`recover_c0` returns `c0` of a polynomial from `t` of its shares").
3. **Checks.** Each contract is checked against the Rust code: unit/property tests, LLM-assisted
   review, or a model checker such as Kani.
4. **Theorems.** We prove properties of how the building blocks compose, from the contracts alone.

The theorems hold for any implementation that satisfies the contracts, so nothing depends on a
faithful translation. The trust boundary is the list of contracts, each with its own check.

What this does not give: a proof that the Rust code satisfies its contracts. That rests on the
checks in step 3.

## Shamir secret sharing (`FastcryptoSpecs/Shamir.lean`)

Black boxes from `fastcrypto-tbls/src/polynomial.rs`: `Poly::rand_fixed_c0`, `eval`, `c0`,
`degree_bound`, `+=`, `recover_c0`.

Theorems (all proved, no `sorry`, only Lean's standard axioms):

| Theorem | Statement |
|---|---|
| `recover_dealt_secret` | Any `t` shares of a secret dealt with `rand_fixed_c0(t - 1, s)` recover `s`. |
| `recover_agrees` | Any two sets of `t` shares of the same dealing recover the same value. |
| `recover_sum_of_dealings` | If every party sums the shares it got from several dealers, any `t` summed shares recover the sum of the dealers' secrets (the core of `complete_dkg`). |
| `shares_independent_of_secret` | The shares at fewer than `t` indices have the same distribution for every secret, so they reveal nothing about it. |

### Contracts and their checks in fastcrypto

| Contract | Rust test today (`fastcrypto-tbls/src/tests/polynomial_tests.rs`) |
|---|---|
| `rand_c0`: `rand_fixed_c0(d, s).c0() == s` | none |
| `rand_degree`: `rand_fixed_c0(d, s).degree_bound() == d` | partial: `test_degree_bound` checks `rand`, not `rand_fixed_c0` |
| `eval_index`: `p.eval(i).index == i` | none |
| `add_eval`: `(p + q).eval(i) == p.eval(i) + q.eval(i)` | partial: `add` checks one index, degrees 3 and 5 |
| `add_c0`: `(p + q).c0() == p.c0() + q.c0()` | none |
| `add_degree`: `(p + q).degree_bound() == max(...)` | none |
| `recover_c0`: `t` distinct shares of `p` with `degree_bound < t` recover `p.c0()` | partial: `test_recover_c0` only uses `degree_bound == t - 1` |
| `vanishing_exists`: for fewer than `t` indices and any `c`, some polynomial of degree bound `≤ t - 1` has `c0() == c` and is zero at those indices | none (test by constructing `c · ∏ₖ (1 - x / iₖ)`) |
| `rand_shift`: `rand_fixed_c0(d, s) + q` is distributed as `rand_fixed_c0(d, s + q.c0())` for `degree_bound(q) ≤ d` | **assumption**: holds if `S::rand` is uniform; check by review, not by unit tests |

`rand_fixed_c0` is modelled as a probability distribution (`PMF`), so the first two contracts
are about every polynomial it can return.

Next step: add one property test per testable contract in fastcrypto.

### Not covered

* Feldman commitments (`commit`, `verify_share`).

## Later

* `FastcryptoSpecs/Avss/` (not built yet): first draft of the AVSS model for threshold Schnorr,
  aiming at "every honest party eventually gets its shares".

## Build

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

CI (`.github/workflows/ci.yml`) runs the same build on every push and pull request.
