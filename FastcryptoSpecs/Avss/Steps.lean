/-
The AVSS functions of fastcrypto-tbls/src/threshold_schnorr/avss.rs as black boxes (`Api`), and
what we expect from them (`Contracts`). Each contract field documents the assumption and how it is
checked against the Rust code ("Check: test" or "Check: review").
-/
import FastcryptoSpecs.Avss.Setup
import FastcryptoSpecs.Shamir

namespace FastcryptoSpecs.Avss

/-- Result of `Receiver::process_message`. -/
inductive Processed (Output Complaint : Type) where
  /-- `Err(InvalidMessage)` or `Err(InvalidInput)`: the message is ignored. -/
  | invalid
  /-- `Ok(ProcessedMessage::Valid(output))`. -/
  | valid (output : Output)
  /-- `Ok(ProcessedMessage::Complaint(complaint))`. -/
  | complaint (complaint : Complaint)

/-- The AVSS API of fastcrypto as black boxes, with the names and inputs/outputs of the Rust
functions and no implementation.

The functions are total, pure and deterministic. In particular:
* a Rust `Err` is `none` (or `Processed.invalid`); a panic cannot be represented, so a contract
  saying a function returns a value also claims that it does not panic on those inputs;
* `process_message` uses an `rng` only to create the complaint's proof; that randomness is
  abstracted away.

All receivers are configured alike: the same `Nodes`, `Parameters`, session id and `commitment`,
and each receiver's encryption key matches its public key in `Nodes`. Several contracts rely on
this; they say so. -/
structure Api (Party : Type) where
  /-- `avss::Message`: the dealer's broadcast (Feldman commitment and encrypted shares). -/
  Message : Type
  /-- `avss::Complaint`. -/
  Complaint : Type
  /-- `avss::ComplaintResponse`. -/
  Response : Type
  /-- `avss::VerifiedComplaintResponse`. -/
  Verified : Type
  /-- `avss::AvssOutput`. -/
  Output : Type
  /-- `avss::SharesForNode`. -/
  Shares : Type
  /-- `Receiver::process_message(message)`, run by receiver `i`. -/
  processMessage : (i : Party) → Message → Processed Output Complaint
  /-- `Receiver::handle_complaint(message, accuser, complaint, my_output)`, run by `j` with its
  own output. `none` is an `Err`. -/
  handleComplaint : (j : Party) → Message → (accuser : Party) → Complaint → Output →
    Option Response
  /-- `Receiver::verify_complaint_response(message, responder, response)`, run by the accuser `i`.
  `none` is an `Err`. -/
  verifyComplaintResponse : (i : Party) → Message → (responder : Party) → Response →
    Option Verified
  /-- The `responder_id` field of `VerifiedComplaintResponse`. -/
  responderId : Verified → Party
  /-- `Receiver::recover(message, responses)`, run by the accuser `i`. `none` is an `Err`. -/
  recover : (i : Party) → Message → List Verified → Option Output
  /-- The `my_shares` field of `AvssOutput`. -/
  shares : Output → Shares
  /-- `SharesForNode::verify(message, share_ids_of(i), i).is_ok()`: the share indices are exactly
  `share_ids_of(i)`, in order, and each share is consistent with the message's Feldman
  commitment. -/
  verifyShares : Message → (i : Party) → Shares → Bool
  /-- `avss::Dealer`. -/
  Dealer : Type
  /-- `Dealer::create_message(rng)`: the messages it can return, over all `rng`s. -/
  createMessage : Dealer → Set Message
  /-- The scalar field. -/
  F : Type
  [instField : Field F]
  /-- `Poly<S>` and its API, as specified in `FastcryptoSpecs.Shamir`. -/
  Sh : Shamir.Api F
  /-- `Nodes::share_ids_of(i)`. -/
  shareIds : Party → List Shamir.ShareIndex
  /-- The `shares` field of `SharesForNode`. -/
  shareList : Shares → List (Shamir.Eval F)

attribute [instance] Api.instField

variable {Party : Type} [DecidableEq Party]

/-- `o` holds valid shares for party `i` on message `m`: its shares pass
`SharesForNode::verify(m, share_ids_of(i), i)`. -/
def Api.ValidOutput (A : Api Party) (m : A.Message) (i : Party) (o : A.Output) : Prop :=
  A.verifyShares m i (A.shares o) = true

/-- `v` was returned by `verify_complaint_response` for accuser `i` on message `m`, for some
responder and response. -/
def Api.IsVerified (A : Api Party) (i : Party) (m : A.Message) (v : A.Verified) : Prop :=
  ∃ j r, A.verifyComplaintResponse i m j r = some v

/-- What we expect from the Rust functions. Each field relates one or two of them. -/
structure Contracts (S : Setup Party) (A : Api Party) : Prop where
  /-- If `process_message` returns `Valid(o)` for receiver `i` on message `m`, then `o`'s shares
  pass `SharesForNode::verify(m, share_ids_of(i), i)`.

  Holds because `verify_message` returns `Some(output)` only after that call succeeds.
  Check: review (immediate from the code). -/
  process_valid : ∀ i m o, A.processMessage i m = .valid o → A.ValidOutput m i o
  /-- For every message `m` and receivers `i`, `j`: `process_message` returns `Err` for `i` if and
  only if it returns `Err` for `j`.

  Holds because every check that returns `Err` depends only on the message and the shared
  configuration (degree and reducedness of the commitment, its constant term against
  `commitment`, the number of ciphertexts, the ciphertext proof); a failure to decrypt or verify
  this receiver's shares returns `Ok(Complaint)` instead. Assumes all receivers use the same
  `commitment` (see `Api`).
  Check: review, plus a test with one malformed message and several receivers. -/
  process_invalid_iff : ∀ i j m,
    A.processMessage i m = .invalid ↔ A.processMessage j m = .invalid
  /-- If `process_message` returns `Complaint(c)` for `i` and `Valid(o)` for `j` on the same
  message `m`, then `handle_complaint` by `j` on `(m, i, c, o)` returns `Ok`.

  Holds because `o`'s commitment is `m`'s, `c`'s recovery package is honestly generated (so its
  proof verifies and it decrypts to the bytes `i` decrypted), and `check_recovered_shares` accepts
  exactly when those bytes do not deserialize or fail `verify`, which is when `process_message`
  returns `Complaint`. Assumes `i`'s encryption key matches its public key in `Nodes` (see `Api`).
  Check: test, with a dealer that corrupts one receiver's shares. -/
  handle_accepts : ∀ i j m c o, A.processMessage i m = .complaint c →
    A.processMessage j m = .valid o → ∃ r, A.handleComplaint j m i c o = some r
  /-- If `process_message` returns `Valid(o)` for `j` on `m`, and `handle_complaint` by `j` on
  `(m, i, c, o)` returns `Ok(r)`, then `verify_complaint_response` by `i` on `(m, j, r)` returns
  `Ok`.

  Holds because `r` carries `o`'s shares, which already passed `verify` for `j`.
  Check: test (same setup as `handle_accepts`). -/
  response_verifies : ∀ i j m c o r, A.processMessage j m = .valid o →
    A.handleComplaint j m i c o = some r → ∃ v, A.verifyComplaintResponse i m j r = some v
  /-- If `verify_complaint_response` by `i` on `(m, j, r)` returns `Ok(v)`, then
  `v.responder_id == j`.

  Check: review (the constructor stores `responder_id`). -/
  verify_binds : ∀ i m j r v, A.verifyComplaintResponse i m j r = some v → A.responderId v = j
  /-- If `process_message` does not return `Err` for `i` on `m`, and `vs` is a list of responses
  that `verify_complaint_response` returned for `i` on `m`, from distinct responders whose total
  weight is at least `t`, then `recover` by `i` on `(m, vs)` returns `Ok`.

  Holds because each verified response has exactly as many shares as its responder's weight, at
  that responder's share indices (which are disjoint across parties), so there are at least `t`
  shares at distinct indices; interpolating shares that pass `verify` against a commitment of
  degree `t - 1` gives shares that pass `verify` too.
  Check: test. -/
  recover_complete : ∀ i m (vs : List A.Verified), A.processMessage i m ≠ .invalid →
    (∀ v ∈ vs, A.IsVerified i m v) → (vs.map A.responderId).Nodup →
    S.t ≤ S.weightOf (vs.map A.responderId).toFinset →
    ∃ o, A.recover i m vs = some o
  /-- If `recover` by `i` on `(m, vs)` returns `Ok(o)`, then `o`'s shares pass
  `SharesForNode::verify(m, share_ids_of(i), i)`, whatever `vs` is.

  Holds because `recover` calls that `verify` on its result before returning `Ok`.
  Check: review (immediate from the code). -/
  recover_sound : ∀ i m (vs : List A.Verified) o, A.recover i m vs = some o → A.ValidOutput m i o
  /-- If `m` is a message `create_message` can return, then `process_message` returns `Valid` for
  every receiver `i` on `m`.

  Assumes the receivers are configured like the dealer (see `Api`).
  Check: test. -/
  create_valid : ∀ d m i, m ∈ A.createMessage d → ∃ o, A.processMessage i m = .valid o
  /-- If `process_message` does not return `Err` for some receiver on `m`, then there is a
  polynomial `p` (a `Poly<S>`) with `degree_bound() < t` such that for every party `j` and every
  `SharesForNode` value `sh` that passes `verify(m, share_ids_of(j), j)`, the shares of `sh` are
  exactly `p.eval(k)` for `k` in `share_ids_of(j)`, in order.

  Holds because the Feldman commitment fixes a unique polynomial "in the exponent" of a
  prime-order group, `verify_message` checks that its degree is `t - 1`, and `verify` checks the
  indices and each value against it.
  Check: review. It is an existence claim, which tests cannot check. -/
  feldman_binding : ∀ i m, A.processMessage i m ≠ .invalid →
    ∃ p, A.Sh.degreeBound p < S.t ∧
      ∀ j sh, A.verifyShares m j sh = true → A.shareList sh = (A.shareIds j).map (A.Sh.eval p)

end FastcryptoSpecs.Avss
