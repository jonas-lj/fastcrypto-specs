/-
AVSS with an honest dealer, i.e. one whose message comes from `Dealer::create_message`: honest
receivers need no complaints, and when the honest receivers alone can certify the message.
-/
import FastcryptoSpecs.Avss.Protocol

namespace FastcryptoSpecs.Avss

variable {Party : Type} [Fintype Party] [DecidableEq Party]
  {S : Setup Party} {A : Api Party}

omit [Fintype Party] in
/-- **Honest dealer: no complaints.** If `m` is a message `create_message` can return, then every
honest party `i` eventually holds an output from `process_message` whose shares pass
`SharesForNode::verify(m, share_ids_of(i), i)`, and `i` never has a complaint about `m`. -/
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

/-- **Honest dealer: certifiable.** If `m` is a message `create_message` can return and the
parties outside `corrupt` have total weight at least `t + f`, then they form a certificate for
`m`. -/
theorem honest_dealer_certifiable (hA : Contracts S A) {d : A.Dealer} {m : A.Message}
    (hm : m ∈ A.createMessage d) {corrupt : Finset Party}
    (hhonest : S.t + S.f ≤ S.weightOf corruptᶜ) :
    Certificate S A corrupt m corruptᶜ where
  weight := hhonest
  honest_signed_valid j _ _ := hA.create_valid d m j hm

/-- **Honest dealer: certifiable when `W ≥ t + 2f`.** If `m` is a message `create_message` can
return and the total weight `W` is at least `t + 2f`, then the parties outside `corrupt` form a
certificate for `m`. -/
theorem honest_dealer_certifiable_of_params (hA : Contracts S A) {d : A.Dealer} {m : A.Message}
    (hm : m ∈ A.createMessage d) {corrupt : Finset Party}
    (hcorrupt : S.Tolerates corrupt) (hW : S.t + 2 * S.f ≤ ∑ i, S.weight i) :
    Certificate S A corrupt m corruptᶜ :=
  honest_dealer_certifiable hA hm (by
    have := S.weightOf_add_compl corrupt
    unfold Setup.Tolerates at hcorrupt
    omega)

/-- **Corrupt parties can block certification.** If the total weight `W` is less than
`t + f + weightOf(corrupt)`, then every set of parties outside `corrupt` has weight less than
`t + f`. So every certificate needs a signature from a corrupt party, and the corrupt parties can
prevent any certificate, including for an honest dealer, by not signing.

With corrupt weight exactly `f`, `hW` is `W < t + 2f`. `Parameters::validate` only requires
`t + f ≤ W`, so it allows this. -/
theorem corrupt_can_block_certificate {corrupt : Finset Party}
    (hW : ∑ i, S.weight i < S.t + S.f + S.weightOf corrupt) (signers : Finset Party)
    (hsigners : ∀ j ∈ signers, j ∉ corrupt) : S.weightOf signers < S.t + S.f := by
  have hsub : signers ⊆ corruptᶜ := fun j hj => Finset.mem_compl.mpr (hsigners j hj)
  have h1 := S.weightOf_mono hsub
  have h2 := S.weightOf_add_compl corrupt
  omega

end FastcryptoSpecs.Avss
