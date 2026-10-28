/-
A toy AVSS and DKG instance, with an execution, that satisfies every hypothesis of the AVSS and DKG
theorems at once, so those hypotheses are consistent.
-/
import FastcryptoSpecs.Avss.Dkg
import FastcryptoSpecs.NonVacuity.Shamir

namespace FastcryptoSpecs.NonVacuity

open FastcryptoSpecs.Avss FastcryptoSpecs.Shamir Polynomial

/-- One party, of weight 2, with `t = 1` and `f = 0`. -/
def toySetup : Setup (Fin 1) := ⟨fun _ => 2, 1, 0⟩

/-- The share indices of the single party: 1 and 2. -/
def toyShareIds (_ : Fin 1) : List ShareIndex := [⟨1, by norm_num⟩, ⟨2, by norm_num⟩]

/-- The shares of `p` for party `i`. -/
noncomputable def toyShares (p : TPoly) (i : Fin 1) : List (Eval F) :=
  (toyShareIds i).map (toyShamir.eval p)

/-- Whether `sh` are exactly the shares of `m` for party `j`. -/
noncomputable def toyVerify (m : TPoly) (j : Fin 1) (sh : List (Eval F)) : Bool :=
  @decide (sh = toyShares m j) (Classical.propDecidable _)

lemma toyVerify_iff {m : TPoly} {j : Fin 1} {sh : List (Eval F)} :
    toyVerify m j sh = true ↔ sh = toyShares m j := by
  simp [toyVerify]

/-- A toy AVSS: the message is the dealer's polynomial itself, it is valid when its degree bound is
below `t = 1`, and there are no complaints. -/
noncomputable def toyAvss : Avss.Api (Fin 1) where
  Message := TPoly
  Complaint := Empty
  Response := Empty
  Verified := Empty
  Output := List (Eval F)
  Shares := List (Eval F)
  processMessage i m := if m.bound < 1 then .valid (toyShares m i) else .invalid
  handleComplaint _ _ _ c _ := c.elim
  verifyComplaintResponse _ _ _ r := r.elim
  responderId v := v.elim
  recover i m _ := if m.bound < 1 then some (toyShares m i) else none
  shares o := o
  verifyShares := toyVerify
  Dealer := Unit
  createMessage _ := {m | m.bound < 1}
  F := F
  Sh := toyShamir
  shareIds := toyShareIds
  shareList sh := sh

/-- Add two share lists position by position, keeping the first list's indices. -/
def addShares (a b : List (Eval F)) : List (Eval F) :=
  List.zipWith (fun x y => ⟨x.index, x.value + y.value⟩) a b

/-- A toy `complete_dkg`: the position-wise sum of the outputs' shares. -/
noncomputable def toyDkg : DkgApi (Fin 1) toyAvss where
  DkOutput := List (Eval F)
  completeDkg os := match os with
    | [] => none
    | o :: rest => some (rest.foldl (fun acc o' => addShares acc o'.2) o.2)
  shares dk := dk

lemma addShares_map (idx : List ShareIndex) (a b : ShareIndex → F) :
    addShares (idx.map fun k => ⟨k, a k⟩) (idx.map fun k => ⟨k, b k⟩) =
      idx.map fun k => ⟨k, a k + b k⟩ := by
  induction idx with
  | nil => rfl
  | cons k idx ih => simp only [addShares, List.map_cons, List.zipWith_cons_cons] at ih ⊢; rw [ih]

lemma foldl_addShares (idx : List ShareIndex) (v : Fin 1 × List (Eval F) → ShareIndex → F)
    (rest : List (Fin 1 × List (Eval F)))
    (hrest : ∀ o ∈ rest, o.2 = idx.map fun k => ⟨k, v o k⟩) (a : ShareIndex → F) :
    rest.foldl (fun acc o' => addShares acc o'.2) (idx.map fun k => ⟨k, a k⟩) =
      idx.map fun k => ⟨k, a k + (rest.map fun o => v o k).sum⟩ := by
  induction rest generalizing a with
  | nil => simp
  | cons o rest ih =>
    rw [List.foldl_cons, hrest o List.mem_cons_self, addShares_map,
      ih (fun o' ho' => hrest o' (List.mem_cons_of_mem _ ho'))]
    simp [add_assoc]

theorem toyAvss_contracts : Avss.Contracts toySetup toyAvss where
  process_valid i m o h := by
    show toyVerify m i o = true
    simp only [toyAvss] at h
    split_ifs at h
    cases h
    exact toyVerify_iff.mpr rfl
  process_invalid_iff i j m := by rw [Subsingleton.elim i j]
  handle_accepts i j m c := c.elim
  response_verifies i j m c o r := r.elim
  verify_binds i m j r v := v.elim
  recover_complete i m vs h _ _ _ := by
    simp only [toyAvss] at h ⊢
    split_ifs at h ⊢ with hb
    · exact ⟨_, rfl⟩
    · exact absurd rfl h
  recover_sound i m vs o h := by
    show toyVerify m i o = true
    simp only [toyAvss] at h
    split_ifs at h
    cases h
    exact toyVerify_iff.mpr rfl
  create_valid d m i hm := by
    simp only [toyAvss] at hm ⊢
    exact ⟨_, if_pos hm⟩
  feldman_binding i m h := by
    simp only [toyAvss] at h
    split_ifs at h with hb
    · refine ⟨m, hb, fun j sh hsh => ?_⟩
      exact toyVerify_iff.mp hsh
    · exact absurd rfl h

theorem toyDkg_contracts : DkgContracts toySetup toyAvss toyDkg where
  complete_sum os dk idx v h hos := by
    match os, h with
    | o :: rest, h =>
      simp only [toyDkg, Option.some.injEq] at h
      subst h
      have h1 : o.2 = idx.map fun k => (⟨k, v o k⟩ : Eval F) := hos o List.mem_cons_self
      show List.foldl (fun acc o' => addShares acc o'.2) o.2 rest = _
      rw [h1]
      exact (foldl_addShares idx v rest (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))
        (v o)).trans rfl
  complete_ok os idx hne _ _ _ := by
    match os, hne with
    | o :: rest, _ => exact ⟨_, rfl⟩

/-- The certified message: the constant polynomial 1. -/
noncomputable def toyMessage : TPoly :=
  ⟨0, C 1, fun m hm => by rw [coeff_C, if_neg (by omega)]⟩

/-- The single party's output. -/
noncomputable def toyOutput : List (Eval F) := toyShares toyMessage 0

/-- The execution: from time 0 on, the party holds and has processed the message, and has its
output. -/
noncomputable def toyState : State toyAvss where
  hasMessage := Set.univ
  processed _ := some (.valid toyOutput)
  complained := ∅
  complaintDelivered := ∅
  responded := ∅
  verified _ := []
  output _ := some toyOutput

lemma toy_process (i : Fin 1) : toyAvss.processMessage i toyMessage = .valid toyOutput := by
  rw [Subsingleton.elim i 0]
  show (if toyMessage.bound < 1 then Processed.valid (toyShares toyMessage 0) else .invalid) = _
  rw [if_pos (show toyMessage.bound < 1 from Nat.zero_lt_one)]
  rfl

theorem toy_run : Run toyAvss toyMessage ∅ (fun _ => toyState) where
  honest _ :=
    { processed_eq := fun i r _ h => by cases h; exact (toy_process i).symm
      stores_valid := fun i o _ h => by cases h; rfl
      verified_ok := fun _ v _ h => by cases h
      verified_nodup := fun _ _ => List.nodup_nil
      output_from := fun i o _ h => by cases h; exact Or.inl rfl }
  grows _ := ⟨fun _ _ h => h, fun _ _ h => h⟩
  gets_message _ _ := ⟨0, Set.mem_univ _⟩
  processes i _ _ _ := ⟨0, _, rfl⟩
  complains i n c _ h := by cases h
  complaint_delivered i j n _ _ h := by cases h
  responds i j n c o r _ h := by cases h
  response_delivered i j r v n _ _ h := by cases h
  recovers i n c o _ h := by cases h

lemma toySetup_valid : toySetup.Valid := ⟨by norm_num [toySetup], by norm_num [toySetup],
  by norm_num [toySetup]⟩

lemma toy_certificate : Certificate toySetup toyAvss ∅ toyMessage Finset.univ :=
  ⟨by norm_num [toySetup, Setup.weightOf], fun j _ _ => ⟨_, toy_process j⟩⟩

/-- **Non-vacuity.** The hypotheses of the AVSS and DKG theorems can all hold at once: there are a
setup, an AVSS API, a `complete_dkg`, a certified message and an execution such that the
parameters are valid, all contracts hold (AVSS, Shamir and DKG), the corrupt set (here empty) is
tolerated, the honest receivers accept a certificate, and the execution is a `Run`. -/
theorem nonvacuous :
    ∃ (S : Setup (Fin 1)) (A : Avss.Api (Fin 1)) (D : DkgApi (Fin 1) A) (m : A.Message)
      (σ : ℕ → State A),
      S.Valid ∧ Avss.Contracts S A ∧ Shamir.Contracts A.Sh ∧ DkgContracts S A D ∧ S.Tolerates ∅ ∧
        Certificate S A ∅ m Finset.univ ∧ Run A m ∅ σ :=
  ⟨toySetup, toyAvss, toyDkg, toyMessage, fun _ => toyState,
    toySetup_valid, toyAvss_contracts, toyShamir_contracts, toyDkg_contracts,
    by simp [Setup.Tolerates, Setup.weightOf], toy_certificate, toy_run⟩

end FastcryptoSpecs.NonVacuity
