# Shamir

Shamir secret sharing as implemented by `fastcrypto_tbls::polynomial::Poly` over scalars.

| File | Contents |
|---|---|
| `Steps.lean` | The functions of `polynomial.rs` as black boxes (`Api`) and what we expect from them (`Contracts`). |
| `Recovery.lean` | `recover_c0` on `t` shares of a dealt polynomial returns the dealt secret, whichever `t` shares are used. |
| `Privacy.lean` | Fewer than `t` shares reveal nothing about the secret. |
| `Dkg.lean` | Summing dealings, the core of `complete_dkg`: the summed shares recover the sum of the secrets. |

`checks.toml` records the fastcrypto revision each contract above was last checked against.

## Theorems

All proved in Lean from the contracts below, with no `sorry` or axioms.

| Theorem | File | Statement |
|---|---|---|
| `recover_dealt_secret` | `Recovery.lean` | `recover_c0` on any `t` distinct shares of `rand_fixed_c0(t - 1, s)` returns `s`. |
| `recover_agrees` | `Recovery.lean` | Any two such sets of `t` shares recover the same secret. |
| `shares_independent_of_secret` | `Privacy.lean` | Fewer than `t` shares have the same distribution for every secret. |
| `recover_sum_of_dealings` | `Dkg.lean` | `recover_c0` on `t` summed shares of several dealings returns the sum of their secrets. |

## Contracts

What the theorems assume about `polynomial.rs`. `checks.toml` records the fastcrypto revision each
was last checked against; the Lean docs are the precise statements.

| Contract | Statement | Checked |
|---|---|---|
| `rand_c0` | `rand_fixed_c0(d, s)` has constant term `s`. | Not yet |
| `rand_degree` | `rand_fixed_c0(d, s)` has `degree_bound() = d`. | Not yet |
| `eval_index` | `p.eval(i)` has index `i`. | Not yet |
| `add_eval`, `add_c0`, `add_degree` | `p + q` evaluates and has constant term `p + q` pointwise, with the larger degree bound. | Not yet |
| `mul_eval`, `mul_c0`, `mul_degree` | `p * a` evaluates and has constant term `p * a` pointwise, with no larger degree bound. | Not yet |
| `recover_c0` | `recover_c0` on `t` distinct evaluations of `p` with `degree_bound() < t` returns `p.c0()`. | Not yet |
| `recover_c0_linear` | On fixed distinct indices, `recover_c0` is a fixed linear combination of the values. | Not yet |
| `rand_shift` | Adding `q` to `rand_fixed_c0(d, s)` gives the distribution of `rand_fixed_c0(d, s + q.c0())`. | Not yet |
| `vanishing_exists` | For fewer than `t` indices there is a polynomial with any constant term that vanishes on them. | Not yet |
