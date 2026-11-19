# AVSS

The AVSS protocol of `fastcrypto_tbls::threshold_schnorr::avss`, DKG and key rotation built on
it. Each file builds on the ones above it.

| File | Contents |
|---|---|
| `Setup.lean` | Parties, weights, `t` and `f` (`Setup`), `weightOf`, `Tolerates`, the checks of `Parameters::validate` (`Valid`), and weight lemmas. |
| `Steps.lean` | The functions of `avss.rs` as black boxes (`Api`) and what we expect from them (`Contracts`). |
| `Protocol.lean` | The execution model and its assumptions (`Certificate`, `State`, `HonestComputes`, `Grows`, `BasicRun`, `Run`), and the liveness theorem `every_honest_party_gets_valid_shares`. |
| `HonestDealer.lean` | A dealer whose message every receiver finds valid, as `create_message`'s is except with probability `≤ 1/|S|`: no complaints, certifiable when the honest weight is at least `t + f`, and corrupt parties can block certification. |
| `Agreement.lean` | All honest outputs fit one polynomial, so any `t` honest shares recover the same secret. |
| `Dkg.lean` | `complete_dkg` as a black box with its contracts (`DkgApi`, `DkgContracts`), and the DKG theorems: it completes, outputs agree, and they share one joint secret. |
| `Tob.lean` | Reading dealer certificates from the total-order broadcast (`Cert`, `accepted`, `Tob`, `TobRun`): honest parties accept the same certificate per dealer and, once done, the same dealers, so the DKG gives one joint secret without assuming that, and they include an honest dealer. |
| `KeyRotation.lean` | Key rotation: the receiver functions with a `commitment` and `complete_key_rotation` as black boxes (`RotationApi`, `RotationContracts`), the instance resharing a share `s` (`RotationApi.at`), and the theorem that the new shares are shares of the old secret. |
| `Liveness.lean` | The TOB over time (`TobLive`): every honest party is eventually done, holds an output from each dealer it accepted, and completes the DKG. |

## Theorems

All proved in Lean from the contracts below and the assumptions in `Protocol.lean`, `Tob.lean`,
`KeyRotation.lean` and `Liveness.lean`, with no `sorry` or axioms. The corrupt parties have weight
at most `f` (`Setup.Tolerates`) and the parameters pass `Parameters::validate` (`Setup.Valid`).

| Theorem | File | Statement |
|---|---|---|
| `every_honest_party_gets_valid_shares` | `Protocol.lean` | Liveness: for a certified message, every honest party eventually holds shares that pass `SharesForNode::verify`, directly or through complaints and `recover`. |
| `honest_dealer_no_complaints` | `HonestDealer.lean` | If every receiver finds the message valid, every honest party gets valid shares from `process_message` and never complains. |
| `honest_dealer_certifiable` | `HonestDealer.lean` | Such a message is certified by the honest parties if their weight is at least `t + f`. |
| `honest_dealer_certifiable_of_params` | `HonestDealer.lean` | The same when `W ≥ t + 2f`. |
| `corrupt_can_block_certificate` | `HonestDealer.lean` | If `W < t + f + weightOf(corrupt)`, every certificate needs a corrupt signer, so the corrupt parties can block even an honest dealer. `validate` allows this. |
| `honest_outputs_agree` | `Agreement.lean` | All honest outputs of a certified message fit one polynomial of degree `< t`. |
| `honest_shares_recover_same_secret` | `Agreement.lean` | Any `t` honest shares at distinct indices give the same `recover_c0`. |
| `honest_dealer_secret_shared` | `Agreement.lean` | For a message from `create_message`, the polynomial all honest outputs fit has the dealer's `secret` as constant term. |
| `dkg_completes` | `Dkg.lean` | `complete_dkg` returns `Ok` for every honest party, given certified dealers of weight `≥ t`. |
| `dkg_outputs_agree` | `Dkg.lean` | Honest `complete_dkg` outputs are shares of the sum of the dealers' polynomials. |
| `dkg_recover_same_secret` | `Dkg.lean` | Any `t` honest DKG shares recover the sum of the dealers' secrets. |
| `accepted_same_cert` | `Tob.lean` | Honest parties accept the same certificate for each dealer. |
| `done_accepted_eq` | `Tob.lean` | Honest parties that are done accept the same dealers. |
| `dkg_recover_same_secret_of_tob` | `Tob.lean` | DKG over the TOB: any `t` honest DKG shares recover one joint secret, without assuming the parties agree on the dealers. |
| `done_has_honest_dealer` | `Tob.lean` | The dealers a party accepts once done include one that is not corrupt. |
| `key_rotation_keeps_secret` | `KeyRotation.lean` | If every honest party combines the outputs of the same `t_old` resharing instances with `complete_key_rotation`, the new shares lie on one polynomial of degree `< t` with the old secret as constant term. |
| `every_honest_party_completes_dkg` | `KeyRotation.lean` | Key rotation: the receiver functions with a `commitment` and `complete_key_rotation` as black boxes (`RotationApi`, `RotationContracts`), the instance resharing a share `s` (`RotationApi.at`), and the theorem that the new shares are shares of the old secret. |
| `Liveness.lean` | DKG liveness: every honest party is eventually done, holds an output from each dealer it accepted, and `complete_dkg` returns `Ok` on them. |

## Contracts

What the theorems assume about the Rust code. `checks.toml` records the fastcrypto revision each
was last checked against; the Lean docs are the precise statements.

| Contract | Statement | Checked |
|---|---|---|
| `process_valid` | `process_message` returning `Valid(o)` ⇒ `o`'s shares verify. | Verus |
| `process_invalid_iff` | `process_message` is `Err` for one receiver iff for all. | Verus |
| `handle_accepts` | A complaint from `process_message` is answered by `handle_complaint` of any receiver with `Valid`. | Verus |
| `response_verifies` | Such a response passes `verify_complaint_response`. | Verus |
| `verify_binds` | A verified response's `responder_id` is the given responder. | Verus |
| `recover_complete` | `recover` succeeds on verified responses from distinct parties of weight `≥ t`. | Verus |
| `recover_sound` | `recover` returning `Ok(o)` ⇒ `o`'s shares verify. | Verus |
| `create_valid` | A message from `create_message` is valid for all receivers except with probability `≤ 1/|S|`. | Not yet |
| `create_secret` | The polynomial a message from `create_message` binds to has the dealer's `secret` as constant term. | Not yet |
| `feldman_binding` | A message accepted by any receiver binds all verifying shares to one polynomial of degree `< t`. | Not yet |
| `complete_sum` | `complete_dkg`'s shares are the sums of the dealers' shares. | Not yet |
| `complete_ok` | `complete_dkg` succeeds on distinct dealers of weight `≥ t` with shares at the same indices. | Not yet |
| `process_matches_commitment` | A message accepted by a receiver with `commitment = g^s` binds to a polynomial with constant term `s`. | Not yet |
| `rotation_interpolates` | Each share from `complete_key_rotation` is `recover_c0` of the outputs' shares at that index. | Not yet |

Key rotation also assumes all contracts of `Contracts` for each resharing instance (`RotationApi.at s`):
its receivers have `commitment = g^s` and its dealers have `secret = s`.

The Verus proofs are in [MystenLabs/fastcrypto#1155](https://github.com/MystenLabs/fastcrypto/pull/1155)
(`verification/`, not merged yet). They rely on trusted specs of the helpers they call, such as
`SharesForNode::verify`, `check_message`, `decrypt_my_shares`, `check_complaint` and
`recover_shares`; `verification/README.md` there lists them.
