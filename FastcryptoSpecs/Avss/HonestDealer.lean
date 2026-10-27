/-
AVSS with an honest dealer: no complaints are needed, and when a certificate can be formed.
-/
import FastcryptoSpecs.Avss.Protocol

namespace FastcryptoSpecs.Avss

variable {Party : Type} [Fintype Party] [DecidableEq Party]
  {S : Setup Party} {A : Api Party}

omit [Fintype Party] in
/-- **Honest dealer: no complaints.** If the dealer's message comes from `create_message`, every
honest receiver eventually holds valid shares straight from the dealer, and no honest receiver
ever has a complaint. Only `BasicRun` is assumed, so this holds whatever happens on the complaint
path (e.g. if no complaint is ever answered). -/
theorem honest_dealer_no_complaints (hA : Contracts S A) {d : A.Dealer} {m : A.Message}
    (hm : m ∈ A.createMessage d) {corrupt : Finset Party} {σ : ℕ → State A}
    (hrun : BasicRun A m corrupt σ) (i : Party) (hi : i ∉ corrupt) :
    (∃ n o, (σ n).output i = some o ∧ A.ValidOutput m i o) ∧
      ∀ n c, (σ n).processed i ≠ some (.complaint c) := by
  obtain ⟨o, ho⟩ := hA.create_valid d m i hm
  refine ⟨?_, fun n c hc => ?_⟩
  · obtain ⟨n0, hn0⟩ := hrun.gets_message i hi
    obtain ⟨n1, r, hr⟩ := hrun.processes i n0 hi hn0
    have hr' := (hrun.honest n1).processed_eq i r hi hr
    rw [ho] at hr'
    subst hr'
    exact ⟨n1, o, (hrun.honest n1).stores_valid i o hi hr, hA.process_valid i m o ho⟩
  · have := (hrun.honest n).processed_eq i _ hi hc
    rw [ho] at this
    cases this

/-- **Honest dealer: certifiable when the honest weight is at least `t + f`.** Then the honest
receivers alone form a certificate for a message from `create_message`: they all get `Valid`.

In Hashi the weights are reduced (`Nodes::knapsack_reduce`), and the reduction guarantees honest
reduced weight `≥ t' + f'` when the corrupt *original* weight is at most `f - δ` (property (L1)
in knapsack_weight_reduction.rs). -/
theorem honest_dealer_certifiable (hA : Contracts S A) {d : A.Dealer} {m : A.Message}
    (hm : m ∈ A.createMessage d) {corrupt : Finset Party}
    (hhonest : S.t + S.f ≤ S.weightOf corruptᶜ) :
    Certificate S A corrupt m corruptᶜ where
  weight := hhonest
  honest_signed_valid j _ _ := hA.create_valid d m j hm

/-- **Honest dealer: certifiable when `W ≥ t + 2f`.** With corrupt weight at most `f`, the honest
weight is at least `W - f ≥ t + f`. -/
theorem honest_dealer_certifiable_of_params (hA : Contracts S A) {d : A.Dealer} {m : A.Message}
    (hm : m ∈ A.createMessage d) {corrupt : Finset Party}
    (hcorrupt : S.weightOf corrupt ≤ S.f) (hW : S.t + 2 * S.f ≤ ∑ i, S.weight i) :
    Certificate S A corrupt m corruptᶜ :=
  honest_dealer_certifiable hA hm (by have := S.weightOf_add_compl corrupt; omega)

/-- **Corrupt parties can block certification when `W < t + f + (corrupt weight)`.** Then no set
of honest signers reaches weight `t + f`, so every certificate needs a signature from a corrupt
party. With corrupt weight `f`, this is exactly `W < t + 2f`, which `Parameters::validate` allows
(it only requires `t + f ≤ W`). -/
theorem corrupt_can_block_certificate {corrupt : Finset Party}
    (hW : ∑ i, S.weight i < S.t + S.f + S.weightOf corrupt) (signers : Finset Party)
    (hsigners : ∀ j ∈ signers, j ∉ corrupt) : S.weightOf signers < S.t + S.f := by
  have hsub : signers ⊆ corruptᶜ := fun j hj => Finset.mem_compl.mpr (hsigners j hj)
  have h1 := S.weightOf_mono hsub
  have h2 := S.weightOf_add_compl corrupt
  omega

end FastcryptoSpecs.Avss
