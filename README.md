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

## AVSS (`FastcryptoSpecs/Avss/`)

One instance of the AVSS protocol from `fastcrypto-tbls/src/threshold_schnorr/avss.rs`, the
building block of the threshold Schnorr DKG.

Black boxes: `process_message`, `handle_complaint`, `verify_complaint_response`, `recover`, and
`SharesForNode::verify` (which defines "valid shares").

**Theorem** (`every_honest_party_gets_valid_shares`, proved): given a certificate of weight
`≥ t + f` for the dealer's message and corrupt weight `≤ f`, every honest receiver eventually
holds shares that pass `SharesForNode::verify` against the certified message, either straight from
the dealer or by recovering them through complaints. The dealer and the corrupt receivers may
behave arbitrarily.

The proof follows the argument in the docs of `Dealer::create_message`: the honest signers have
weight `≥ t`, they hold valid shares, they answer every honest complaint, and their responses are
enough for `recover`.

### Honest dealers (`HonestDealer.lean`)

| Theorem | Statement |
|---|---|
| `honest_dealer_no_complaints` | If the message comes from `create_message`, every honest receiver eventually holds valid shares straight from the dealer, and none ever has a complaint. Assumes only `BasicRun` (get and process the message), so it holds whatever happens on the complaint path. |
| `honest_dealer_certifiable` | If the honest weight is `≥ t + f`, the honest receivers alone form a certificate for an honest dealer. |
| `honest_dealer_certifiable_of_params` | Corollary: this holds when corrupt weight `≤ f` and `W ≥ t + 2f`. |
| `corrupt_can_block_certificate` | If `W < t + f + (corrupt weight)`, no set of honest signers reaches `t + f`, so corrupt parties can block an honest dealer by not signing. |

`Parameters::validate` only requires `t + f ≤ W`, so `W ≥ t + 2f` is an extra condition. Hashi
sets `t = W - 2f` before weight reduction, so it holds there with equality. After
`Nodes::knapsack_reduce` it need not hold for the reduced `(t', f', W')`, as
knapsack_weight_reduction.rs documents. Instead the reduction guarantees honest reduced weight
`≥ t' + f'` when the corrupt original weight is at most `f - δ`, which is the hypothesis of
`honest_dealer_certifiable`.

### Contracts (`Steps.lean`)

| Contract | Statement |
|---|---|
| `process_valid` | a `Valid` result from `process_message` passes `SharesForNode::verify` |
| `process_invalid_iff` | whether `process_message` rejects a message outright is the same for all receivers |
| `handle_accepts` | a complaint from `process_message` is accepted by `handle_complaint` of any receiver whose `process_message` returned `Valid` |
| `response_verifies` | that receiver's response passes `verify_complaint_response` at the accuser |
| `verify_binds` | `verify_complaint_response` binds the response to the responder it came from |
| `recover_complete` | `recover` succeeds on verified responses from distinct responders of weight `≥ t` |
| `recover_sound` | `recover` only returns shares that pass `SharesForNode::verify` (its final check) |
| `create_valid` | every receiver gets `Valid` on a message from `create_message` (same nodes, parameters, session id and `commitment` as the dealer) |

### Protocol assumptions (`Protocol.lean`)

*Certificate*: receivers check its weight (`≥ t + f`), honest receivers sign only `Valid` messages,
and all honest receivers use the same (first) certificate per dealer.

*Honest behaviour* (`HonestComputes`): honest receivers store what the steps return, collect only
verified responses, at most one per responder.

*Liveness obligations* (`Run`), each "a step that can be taken eventually is":

| Obligation | Documented in avss.rs? |
|---|---|
| `gets_message`: every honest receiver eventually has the **certified** message | **no**, see below |
| `processes`: it runs `process_message` on it | yes |
| `complains`: with a complaint, it broadcasts it once the certificate is on the TOB | yes |
| `complaint_delivered`: broadcast complaints reach every honest receiver | network assumption |
| `responds`: a receiver with a valid output keeps it and answers complaints | yes |
| `response_delivered`: responses between honest parties arrive and are collected if verified | network assumption |
| `recovers`: an accuser calls `recover` once it succeeds | yes |

### Obligations not stated in avss.rs, and how Hashi meets them

The model needs two caller obligations that the avss.rs docs do not state:

1. **Getting the certified message** (`gets_message`). A corrupt dealer can withhold its message
   from an honest receiver and still collect `t + f` signatures from others; without the message
   the receiver can neither process it nor complain.
2. **Processing the certified message after equivocation.** A corrupt dealer can send different
   messages to different receivers; an honest receiver must process the one that was certified.

Hashi (`origin/main` at `0181e0c9d`, 2026-10-26) meets both in `run_dkg_as_party`
(`crates/hashi/src/mpc/mpc_except_signing.rs`): when a certificate arrives on the TOB and the
receiver's stored message for that dealer is missing *or has a different hash* than the
certificate's `messages_hash`, it retrieves the message from the certificate's signers, drops any
output computed from the old message, and processes the certified one.

* Retrieval (`hedged_retrieve`) accepts a response only if it hashes to the certified
  `messages_hash` (`rpc/response_checks.rs::certified_retrieval`, `message_cache.rs::certified`),
  so corrupt signers cannot substitute a message.
* Signers persist the message before signing it (`persist_and_cache_dkg_entry` before
  `sign_dkg_message`), and the honest signers have weight `≥ t ≥ 1`, so some signer can serve it.
* Retrieval asks each signer a bounded number of times. If all fail, the DKG run fails and
  `service.rs` retries the whole MPC protocol after a sleep, which is what makes "eventually" hold.

Suggestion for fastcrypto: state both obligations in the docs of `Receiver::process_message`.

### Not covered yet

* That all honest receivers' shares fit one polynomial of degree `t - 1`, i.e. any `t` of them
  recover the same secret. This needs a contract linking `SharesForNode::verify` to the Shamir
  spec (Feldman commitments).
* Consistency of the hypotheses: a concrete execution satisfying `Run`, to show the theorem is not
  vacuous.
* `complete_dkg`, key rotation, and batch AVSS with AVID.

## Build

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

CI (`.github/workflows/ci.yml`) runs the same build on every push and pull request.
