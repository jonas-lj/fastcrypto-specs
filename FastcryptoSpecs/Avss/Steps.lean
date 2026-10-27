/-
The fastcrypto AVSS receiver functions as black boxes, and their contracts.

Each step has the name and the inputs/outputs of its Rust counterpart in
fastcrypto-tbls/src/threshold_schnorr/avss.rs. Nothing here says how a step computes its result:
the protocol proof only uses `Contracts`, which relate the functions to each other. Each contract
should be checked against the Rust code (see README).
-/
import FastcryptoSpecs.Avss.Setup

namespace FastcryptoSpecs.Avss

/-- Result of `Receiver::process_message`. -/
inductive Processed (Output Complaint : Type) where
  /-- `Err(InvalidMessage)` or `Err(InvalidInput)`: the message is ignored. -/
  | invalid
  /-- `Ok(ProcessedMessage::Valid(output))`. -/
  | valid (output : Output)
  /-- `Ok(ProcessedMessage::Complaint(complaint))`. -/
  | complaint (complaint : Complaint)

/-- The AVSS receiver API of fastcrypto. -/
structure Api (Party : Type) where
  /-- `avss::Message`: the dealer's broadcast. -/
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
  /-- `Receiver::process_message`, run by receiver `i`. -/
  processMessage : (i : Party) → Message → Processed Output Complaint
  /-- `Receiver::handle_complaint`, run by `j` on the complaint of `accuser`, using `j`'s own
  output. `none` is an `Err`. -/
  handleComplaint : (j : Party) → Message → (accuser : Party) → Complaint → Output →
    Option Response
  /-- `Receiver::verify_complaint_response`, run by the accuser `i` on a response from
  `responder`. -/
  verifyComplaintResponse : (i : Party) → Message → (responder : Party) → Response →
    Option Verified
  /-- The `responder_id` field of `VerifiedComplaintResponse`. -/
  responderId : Verified → Party
  /-- `Receiver::recover`, run by the accuser `i`. -/
  recover : (i : Party) → Message → List Verified → Option Output
  /-- The `my_shares` field of `AvssOutput`. -/
  shares : Output → Shares
  /-- `SharesForNode::verify(message, share_ids_of(i), i)`: the shares are the ones party `i`
  should hold according to the dealer's (Feldman) commitment in the message. -/
  verifyShares : Message → (i : Party) → Shares → Bool

variable {Party : Type} [DecidableEq Party]

/-- An output holds valid shares for party `i`: they pass `SharesForNode::verify` against the
dealer's message. -/
def Api.ValidOutput (A : Api Party) (m : A.Message) (i : Party) (o : A.Output) : Prop :=
  A.verifyShares m i (A.shares o) = true

/-- `v` was returned by `verify_complaint_response` for accuser `i` on message `m`. -/
def Api.IsVerified (A : Api Party) (i : Party) (m : A.Message) (v : A.Verified) : Prop :=
  ∃ j r, A.verifyComplaintResponse i m j r = some v

/-- What we expect from the Rust functions, only by relating them to each other. -/
structure Contracts (S : Setup Party) (A : Api Party) : Prop where
  /-- `process_message`: a `Valid` output holds valid shares. -/
  process_valid : ∀ i m o, A.processMessage i m = .valid o → A.ValidOutput m i o
  /-- `process_message`: whether a message is rejected outright does not depend on the receiver
  (all receivers use the same `commitment`). -/
  process_invalid_iff : ∀ i j m,
    A.processMessage i m = .invalid ↔ A.processMessage j m = .invalid
  /-- `handle_complaint`: a complaint returned by `process_message` is accepted by a receiver
  that got a valid output for the same message. -/
  handle_accepts : ∀ i j m c o, A.processMessage i m = .complaint c →
    A.processMessage j m = .valid o → ∃ r, A.handleComplaint j m i c o = some r
  /-- `handle_complaint` + `verify_complaint_response`: the response of a receiver with a valid
  output passes the accuser's verification. -/
  response_verifies : ∀ i j m c o r, A.processMessage j m = .valid o →
    A.handleComplaint j m i c o = some r → ∃ v, A.verifyComplaintResponse i m j r = some v
  /-- `verify_complaint_response` binds the response to the responder it came from. -/
  verify_binds : ∀ i m j r v, A.verifyComplaintResponse i m j r = some v → A.responderId v = j
  /-- `recover` succeeds on verified responses from distinct responders of weight at least `t`,
  for a message that is not rejected outright. -/
  recover_complete : ∀ i m (vs : List A.Verified), A.processMessage i m ≠ .invalid →
    (∀ v ∈ vs, A.IsVerified i m v) → (vs.map A.responderId).Nodup →
    S.t ≤ S.weightOf (vs.map A.responderId).toFinset →
    ∃ o, A.recover i m vs = some o
  /-- `recover` only returns valid shares (its final `verify` call). -/
  recover_sound : ∀ i m (vs : List A.Verified) o, A.recover i m vs = some o → A.ValidOutput m i o

end FastcryptoSpecs.Avss
