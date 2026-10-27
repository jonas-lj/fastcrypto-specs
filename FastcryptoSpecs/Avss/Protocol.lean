/-
One AVSS instance: the dealer's certified message, the honest receivers, and the liveness
theorem "every honest receiver eventually holds valid shares".

The protocol steps follow the numbered steps in the docs of avss.rs:
1. the dealer's message is broadcast; receivers process it and sign it if their shares are valid;
   a certificate of weight `t + f` is posted on the total-order broadcast (TOB);
2. a receiver with invalid shares broadcasts its complaint once the certificate is on the TOB;
3. receivers with valid shares answer complaints with their shares;
4. the accuser verifies the responses and recovers its shares from weight `t` of them.

The dealer and the corrupt receivers may behave arbitrarily. We only constrain what honest
parties store (`HonestComputes`) and require that the honest steps and the network eventually
make progress (`Run`).
-/
import FastcryptoSpecs.Avss.Steps

namespace FastcryptoSpecs.Avss

variable {Party : Type} [Fintype Party] [DecidableEq Party]

/-- The certificate for message `m` that all honest receivers accept: the first one from this
dealer on the TOB. -/
structure Certificate (S : Setup Party) (A : Api Party) (corrupt : Finset Party)
    (m : A.Message) (signers : Finset Party) : Prop where
  /-- Receivers check the weight of a certificate before accepting it. -/
  weight : S.t + S.f ≤ S.weightOf signers
  /-- An honest receiver signs a message only if `process_message` returned `Valid`
  (and signatures cannot be forged). -/
  honest_signed_valid : ∀ j ∈ signers, j ∉ corrupt → ∃ o, A.processMessage j m = .valid o

/-- What the parties hold at some point in time, for the certified message. -/
structure State (A : Api Party) where
  /-- Receivers that have the certified message. -/
  hasMessage : Set Party
  /-- The result of `process_message` on the certified message, once a receiver has run it. -/
  processed : Party → Option (Processed A.Output A.Complaint)
  /-- Receivers that have broadcast their complaint. -/
  complained : Set Party
  /-- `(accuser, j)`: `j` has received the accuser's complaint. -/
  complaintDelivered : Set (Party × Party)
  /-- `(j, accuser, response)`: `j` has sent its response to the accuser. -/
  responded : Set (Party × Party × A.Response)
  /-- The verified responses an accuser has collected. -/
  verified : Party → List A.Verified
  /-- A receiver's final output. -/
  output : Party → Option A.Output

/-- Honest receivers store what the fastcrypto steps return. -/
structure HonestComputes (A : Api Party) (m : A.Message) (corrupt : Finset Party)
    (s : State A) : Prop where
  processed_eq : ∀ i r, i ∉ corrupt → s.processed i = some r → r = A.processMessage i m
  /-- A `Valid` result is stored as the output. -/
  stores_valid : ∀ i o, i ∉ corrupt → s.processed i = some (.valid o) → s.output i = some o
  /-- Only responses that passed `verify_complaint_response` are collected... -/
  verified_ok : ∀ i v, i ∉ corrupt → v ∈ s.verified i → A.IsVerified i m v
  /-- ...and at most one per responder. -/
  verified_nodup : ∀ i, i ∉ corrupt → ((s.verified i).map A.responderId).Nodup
  /-- An output comes from `process_message` or from `recover`. -/
  output_from : ∀ i o, i ∉ corrupt → s.output i = some o →
    s.processed i = some (.valid o) ∨ ∃ vs, A.recover i m vs = some o

/-- Parties do not forget results or responses. -/
structure Grows (A : Api Party) (s s' : State A) : Prop where
  processed : ∀ i r, s.processed i = some r → s'.processed i = some r
  verified : ∀ i v, v ∈ s.verified i → v ∈ s'.verified i

/-- An execution `σ` (the state at each point in time) for the certified message `m`, without the
complaint path: honest receivers store what the steps return, and eventually get and process the
certified message. -/
structure BasicRun (A : Api Party) (m : A.Message) (corrupt : Finset Party) (σ : ℕ → State A) :
    Prop where
  honest : ∀ n, HonestComputes A m corrupt (σ n)
  grows : ∀ n, Grows A (σ n) (σ (n + 1))
  /-- Every honest receiver eventually has the certified message (from the dealer's broadcast,
  or fetched from a signer). -/
  gets_message : ∀ i, i ∉ corrupt → ∃ n, i ∈ (σ n).hasMessage
  /-- An honest receiver eventually runs `process_message` on it. -/
  processes : ∀ i n, i ∉ corrupt → i ∈ (σ n).hasMessage → ∃ n' r, (σ n').processed i = some r

/-- A `BasicRun` plus the complaint path. Each field is a liveness obligation of the honest
parties or the network: a step that can be taken eventually is. -/
structure Run (A : Api Party) (m : A.Message) (corrupt : Finset Party) (σ : ℕ → State A) : Prop
    extends BasicRun A m corrupt σ where
  /-- An honest receiver with a complaint eventually broadcasts it (after the certificate). -/
  complains : ∀ i n c, i ∉ corrupt → (σ n).processed i = some (.complaint c) →
    ∃ n', i ∈ (σ n').complained
  /-- A broadcast complaint eventually reaches every honest receiver. -/
  complaint_delivered : ∀ i j n, i ∉ corrupt → j ∉ corrupt → i ∈ (σ n).complained →
    ∃ n', (i, j) ∈ (σ n').complaintDelivered
  /-- An honest receiver with a valid output (kept since processing) answers a complaint it
  received if `handle_complaint` accepts it. -/
  responds : ∀ i j n c o r, j ∉ corrupt → (i, j) ∈ (σ n).complaintDelivered →
    A.processMessage i m = .complaint c → A.processMessage j m = .valid o →
    A.handleComplaint j m i c o = some r → ∃ n', (j, i, r) ∈ (σ n').responded
  /-- A response between honest parties is eventually delivered, and collected if it passes
  `verify_complaint_response` (unless the accuser already has one from that responder). -/
  response_delivered : ∀ i j r v n, i ∉ corrupt → j ∉ corrupt → (j, i, r) ∈ (σ n).responded →
    A.verifyComplaintResponse i m j r = some v →
    ∃ n', ∃ v' ∈ (σ n').verified i, A.responderId v' = j
  /-- An accuser eventually calls `recover` once it succeeds, and stores the result. -/
  recovers : ∀ i n c o, i ∉ corrupt → (σ n).processed i = some (.complaint c) →
    A.recover i m ((σ n).verified i) = some o → ∃ n' o', (σ n').output i = some o'

section Lemmas

variable {A : Api Party} {m : A.Message} {corrupt : Finset Party} {σ : ℕ → State A}

omit [Fintype Party] [DecidableEq Party] in
lemma Run.processed_mono (h : Run A m corrupt σ) {n n' : ℕ} (hle : n ≤ n') {i r}
    (hr : (σ n).processed i = some r) : (σ n').processed i = some r := by
  induction n', hle using Nat.le_induction with
  | base => exact hr
  | succ k _ ih => exact (h.grows k).processed i r ih

omit [Fintype Party] [DecidableEq Party] in
lemma Run.verified_mono (h : Run A m corrupt σ) {n n' : ℕ} (hle : n ≤ n') {i v}
    (hv : v ∈ (σ n).verified i) : v ∈ (σ n').verified i := by
  induction n', hle using Nat.le_induction with
  | base => exact hv
  | succ k _ ih => exact (h.grows k).verified i v ih

omit [Fintype Party] in
/-- Eventually-true facts that stay true hold together at some point. -/
lemma eventually_all (T : Finset Party) (P : Party → ℕ → Prop)
    (mono : ∀ j n n', n ≤ n' → P j n → P j n') (h : ∀ j ∈ T, ∃ n, P j n) :
    ∃ N, ∀ j ∈ T, P j N := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T _ ih =>
    obtain ⟨N, hN⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨na, ha⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨max N na, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact mono _ _ _ (le_max_right _ _) ha
    · exact mono _ _ _ (le_max_left _ _) (hN j hj)

omit [Fintype Party] in
/-- Whatever an honest receiver outputs is valid. -/
lemma output_valid {S : Setup Party} (hA : Contracts S A) {s : State A}
    (hs : HonestComputes A m corrupt s) {i : Party} (hi : i ∉ corrupt) {o : A.Output}
    (ho : s.output i = some o) : A.ValidOutput m i o := by
  rcases hs.output_from i o hi ho with hp | ⟨vs, hvs⟩
  · exact hA.process_valid i m o (hs.processed_eq i _ hi hp).symm
  · exact hA.recover_sound i m vs o hvs

end Lemmas

/-- **Liveness of AVSS.** Given a certificate for the dealer's message `m` (as checked by the
receivers) and Byzantine weight at most `f`, every honest receiver eventually holds valid shares
for `m`, either directly from the dealer or by recovering them through complaints. -/
theorem every_honest_party_gets_valid_shares {S : Setup Party} {A : Api Party}
    (hS : S.Valid) (hA : Contracts S A) {corrupt : Finset Party}
    (hcorrupt : S.weightOf corrupt ≤ S.f) {m : A.Message} {signers : Finset Party}
    (hcert : Certificate S A corrupt m signers) {σ : ℕ → State A}
    (hrun : Run A m corrupt σ) (i : Party) (hi : i ∉ corrupt) :
    ∃ n o, (σ n).output i = some o ∧ A.ValidOutput m i o := by
  -- The honest signers have weight at least `t`, so there is at least one.
  set H := signers.filter (· ∉ corrupt) with hHdef
  have hH : S.t ≤ S.weightOf H := S.honest_signers_weight signers corrupt hcert.weight hcorrupt
  have hHne : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hempty
    rw [hempty] at hH
    simp [Setup.weightOf] at hH
    exact absurd hH (by have := hS.f_lt_t; omega)
  have honestOfH : ∀ j ∈ H, j ∉ corrupt ∧ ∃ o, A.processMessage j m = .valid o := by
    intro j hj
    obtain ⟨hjs, hjc⟩ := Finset.mem_filter.mp hj
    exact ⟨hjc, hcert.honest_signed_valid j hjs hjc⟩
  -- Since an honest signer got a valid output, the message is not rejected outright.
  obtain ⟨j0, hj0⟩ := hHne
  obtain ⟨_, o0, ho0⟩ := honestOfH j0 hj0
  have hnotInvalid : A.processMessage i m ≠ .invalid := by
    intro hinv
    rw [(hA.process_invalid_iff i j0 m).mp hinv] at ho0
    cases ho0
  -- Receiver `i` eventually processes the message.
  obtain ⟨n0, hn0⟩ := hrun.gets_message i hi
  obtain ⟨n1, r, hr⟩ := hrun.processes i n0 hi hn0
  have hr' := (hrun.honest n1).processed_eq i r hi hr
  cases hpm : A.processMessage i m with
  | invalid => exact absurd hpm hnotInvalid
  | valid o =>
    -- Valid shares straight from the dealer.
    rw [hpm] at hr'
    subst hr'
    have ho := (hrun.honest n1).stores_valid i o hi hr
    exact ⟨n1, o, ho, output_valid hA (hrun.honest n1) hi ho⟩
  | complaint c =>
    rw [hpm] at hr'
    subst hr'
    obtain ⟨n2, hn2⟩ := hrun.complains i n1 c hi hr
    -- Every honest signer's response eventually reaches `i` and is collected.
    have hall : ∀ j ∈ H, ∃ n, ∃ v ∈ (σ n).verified i, A.responderId v = j := by
      intro j hj
      obtain ⟨hjc, oj, hoj⟩ := honestOfH j hj
      obtain ⟨n3, hn3⟩ := hrun.complaint_delivered i j n2 hi hjc hn2
      obtain ⟨rj, hrj⟩ := hA.handle_accepts i j m c oj hpm hoj
      obtain ⟨n4, hn4⟩ := hrun.responds i j n3 c oj rj hjc hn3 hpm hoj hrj
      obtain ⟨v, hv⟩ := hA.response_verifies i j m c oj rj hoj hrj
      exact hrun.response_delivered i j rj v n4 hi hjc hn4 hv
    obtain ⟨N, hN⟩ := eventually_all H
      (fun j n => ∃ v ∈ (σ n).verified i, A.responderId v = j)
      (fun j n n' hle ⟨v, hv, hvj⟩ => ⟨v, hrun.verified_mono hle hv, hvj⟩) hall
    -- At time `N'` the accuser still has its complaint and has responses from all of `H`.
    set N' := max N n1
    have hproc : (σ N').processed i = some (.complaint c) :=
      hrun.processed_mono (le_max_right _ _) hr
    set vs := (σ N').verified i
    have hcover : H ⊆ (vs.map A.responderId).toFinset := by
      intro j hj
      obtain ⟨v, hv, hvj⟩ := hN j hj
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨v, hrun.verified_mono (le_max_left _ _) hv, hvj⟩
    obtain ⟨o, ho⟩ := hA.recover_complete i m vs hnotInvalid
      (fun v hv => (hrun.honest N').verified_ok i v hi hv)
      ((hrun.honest N').verified_nodup i hi)
      (le_trans hH (S.weightOf_mono hcover))
    obtain ⟨n', o', ho'⟩ := hrun.recovers i N' c o hi hproc ho
    exact ⟨n', o', ho', output_valid hA (hrun.honest n') hi ho'⟩

end FastcryptoSpecs.Avss
