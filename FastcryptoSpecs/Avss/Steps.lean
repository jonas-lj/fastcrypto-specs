/-
The fastcrypto AVSS functions as black boxes, the meaning of their outputs, and their contracts.

Each step has the name and the inputs/outputs of its Rust counterpart in
fastcrypto-tbls/src/threshold_schnorr/avss.rs. Nothing here says how a step computes its result:
the protocol proof only uses the contracts in `Contracts`, each of which should be backed by a
test (or proof) against the Rust function.
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

/-- The AVSS receiver API of fastcrypto, plus the meaning of its outputs. -/
structure Avss (Party : Type) where
  /-- `avss::Message`: the dealer's broadcast (Feldman commitment + encrypted shares). -/
  Message : Type
  /-- `avss::Complaint`. -/
  Complaint : Type
  /-- `avss::ComplaintResponse`. -/
  Response : Type
  /-- `avss::VerifiedComplaintResponse`. -/
  Verified : Type
  /-- `avss::AvssOutput`. -/
  Output : Type
  /-- `Receiver::process_message`, run by receiver `i`. -/
  processMessage : Party → Message → Processed Output Complaint
  /-- `Receiver::handle_complaint`, run by responder `j` on the complaint of `accuser`, using
  `j`'s own output. `none` is an `Err`. -/
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
  /-- The scalar field. -/
  F : Type
  [instField : Field F]
  /-- The polynomial a message's Feldman commitment commits to. -/
  poly : Message → Polynomial F
  /-- `Nodes::share_ids_of`: the share indices of a party. -/
  shareIds : Party → Finset ℕ
  /-- The share an output holds for a share index (`SharesForNode::share_for_index`). -/
  share : Output → ℕ → Option F
  /-- The message passes the receiver-independent checks of `verify_message` (degree `t - 1`,
  reduced, ciphertext well-formed, matching `commitment`). -/
  wellFormed : Message → Prop

attribute [instance] Avss.instField

variable {Party : Type}

/-- An output holds valid shares for party `i`: for each of `i`'s share indices, the share is the
committed polynomial evaluated at that index. -/
def Avss.ValidOutput (A : Avss Party) (m : A.Message) (i : Party) (o : A.Output) : Prop :=
  ∀ k ∈ A.shareIds i, A.share o k = some ((A.poly m).eval (k : A.F))

/-- A verified response for accuser `i` on message `m` (an output of `verify_complaint_response`). -/
def Avss.IsVerified (A : Avss Party) (i : Party) (m : A.Message) (v : A.Verified) : Prop :=
  ∃ j r, A.verifyComplaintResponse i m j r = some v

/-- What the protocol proof assumes about the Rust functions. Each field is a property of one
function, to be checked against fastcrypto (see README). -/
structure Contracts (S : Setup Party) (A : Avss Party) : Prop where
  /-- `process_message`: a `Valid` output holds valid shares. -/
  process_valid : ∀ i m o, A.processMessage i m = .valid o → A.ValidOutput m i o
  /-- `process_message`: a message is rejected outright exactly when it is not well-formed;
  this does not depend on the receiver (all receivers use the same `commitment`). -/
  process_invalid_iff : ∀ i m, A.processMessage i m = .invalid ↔ ¬ A.wellFormed m
  /-- `verify_message`: a well-formed message commits to a polynomial of degree `t - 1`. -/
  wellFormed_degree : ∀ m, A.wellFormed m → (A.poly m).natDegree < S.t
  /-- `handle_complaint`: a complaint returned by `process_message` is accepted by a receiver
  that holds a valid output for the same message. -/
  handle_accepts : ∀ i j m c o, A.processMessage i m = .complaint c →
    A.processMessage j m = .valid o → ∃ r, A.handleComplaint j m i c o = some r
  /-- `handle_complaint` + `verify_complaint_response`: the response of a receiver with a valid
  output passes the accuser's verification. -/
  response_verifies : ∀ i j m c o r, A.processMessage j m = .valid o →
    A.handleComplaint j m i c o = some r → ∃ v, A.verifyComplaintResponse i m j r = some v
  /-- `verify_complaint_response` binds the response to the responder it came from. -/
  verify_binds : ∀ i m j r v, A.verifyComplaintResponse i m j r = some v → A.responderId v = j
  /-- `recover` succeeds on verified responses from distinct responders of weight at least `t`. -/
  recover_complete : ∀ i m (vs : List A.Verified), A.wellFormed m →
    (∀ v ∈ vs, A.IsVerified i m v) → (vs.map A.responderId).Nodup →
    S.t ≤ S.weightOf (vs.map A.responderId).toFinset →
    ∃ o, A.recover i m vs = some o
  /-- `recover` only returns valid shares when given verified responses. -/
  recover_sound : ∀ i m (vs : List A.Verified) o, A.wellFormed m →
    (∀ v ∈ vs, A.IsVerified i m v) → A.recover i m vs = some o → A.ValidOutput m i o

end FastcryptoSpecs.Avss
