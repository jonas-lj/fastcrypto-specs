# AVSS

The AVSS protocol of `fastcrypto_tbls::threshold_schnorr::avss`, and DKG built on it. Each file
imports the one above it.

| File | Contents |
|---|---|
| `Setup.lean` | Parties, weights, `t` and `f` (`Setup`), `weightOf`, `Tolerates`, the checks of `Parameters::validate` (`Valid`), and weight lemmas. |
| `Steps.lean` | The functions of `avss.rs` as black boxes (`Api`) and what we expect from them (`Contracts`). |
| `Protocol.lean` | The execution model and its assumptions (`Certificate`, `State`, `HonestComputes`, `Grows`, `BasicRun`, `Run`), and the liveness theorem `every_honest_party_gets_valid_shares`. |
| `HonestDealer.lean` | A dealer whose message comes from `create_message`: no complaints, certifiable when the honest weight is at least `t + f`, and corrupt parties can block certification. |
| `Agreement.lean` | All honest outputs fit one polynomial, so any `t` honest shares recover the same secret. |
| `Dkg.lean` | `complete_dkg` as a black box with its contracts (`DkgApi`, `DkgContracts`), and the DKG theorems: it completes, outputs agree, and they share one joint secret. |
