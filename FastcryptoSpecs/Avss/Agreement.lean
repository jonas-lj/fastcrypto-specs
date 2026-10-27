/-
AVSS agreement: all honest receivers' shares fit one polynomial of degree below `t`, so any `t` of
them recover the same secret.
-/
import FastcryptoSpecs.Avss.Protocol

namespace FastcryptoSpecs.Avss

variable {Party : Type} [Fintype Party] [DecidableEq Party]
  {S : Setup Party} {A : Api Party}

/-- Under `hS`, `hA`, `hcorrupt` and `hcert` (as in `every_honest_party_gets_valid_shares`),
`process_message` does not return `Err` for any party on the certified message `m`: some honest
signer got `Valid` on it, and rejection is the same for all receivers. -/
lemma certified_not_invalid (hS : S.Valid) (hA : Contracts S A) {corrupt : Finset Party}
    (hcorrupt : S.weightOf corrupt ≤ S.f) {m : A.Message} {signers : Finset Party}
    (hcert : Certificate S A corrupt m signers) (i : Party) :
    A.processMessage i m ≠ .invalid := by
  have hH : S.t ≤ S.weightOf (signers.filter (· ∉ corrupt)) :=
    S.honest_signers_weight signers corrupt hcert.weight hcorrupt
  obtain ⟨j, hj⟩ : (signers.filter (· ∉ corrupt)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hH
    simp [Setup.weightOf] at hH
    have := hS.f_lt_t
    omega
  obtain ⟨hjs, hjc⟩ := Finset.mem_filter.mp hj
  obtain ⟨o, ho⟩ := hcert.honest_signed_valid j hjs hjc
  intro hinv
  rw [(hA.process_invalid_iff i j m).mp hinv] at ho
  cases ho

/-- **Agreement.** Assume:
* `hS`: the parameters pass `Parameters::validate`;
* `hA`: the fastcrypto functions satisfy their contracts;
* `hcorrupt`: the Byzantine parties `corrupt` have total weight at most `f`;
* `hcert`: honest receivers accept a certificate for message `m` from `signers`;
* `hrun`: the execution `σ` meets the assumptions of `BasicRun`. None of the complaint assumptions
  of `Run` are needed.

Then there is a polynomial `p` with `degree_bound() < t` such that, at every time `n`, every
output `o` held by an honest party `i` has shares equal to `p.eval(k)` for `k` in
`share_ids_of(i)`, in order. This holds whether `o` came from `process_message` or from `recover`.
(`i₀` is any party; it only names the receiver used to apply `feldman_binding`.) -/
theorem honest_outputs_agree (hS : S.Valid) (hA : Contracts S A) {corrupt : Finset Party}
    (hcorrupt : S.weightOf corrupt ≤ S.f) {m : A.Message} {signers : Finset Party}
    (hcert : Certificate S A corrupt m signers) {σ : ℕ → State A}
    (hrun : BasicRun A m corrupt σ) (i₀ : Party) :
    ∃ p, A.Sh.degreeBound p < S.t ∧ ∀ i n o, i ∉ corrupt → (σ n).output i = some o →
      A.shareList (A.shares o) = (A.shareIds i).map (A.Sh.eval p) := by
  obtain ⟨p, hdeg, hbind⟩ :=
    hA.feldman_binding i₀ m (certified_not_invalid hS hA hcorrupt hcert i₀)
  exact ⟨p, hdeg, fun i n o hi ho =>
    hbind i _ (output_valid hA (hrun.honest n) hi ho)⟩

/-- **Same secret.** Assume the hypotheses of `honest_outputs_agree`, and that the Shamir
functions satisfy their contracts (`hSh`). Then there is a polynomial `p` such that for every list
`es` of exactly `t` shares at distinct indices, each taken from an output that some honest party
holds at some time, `recover_c0(t, es)` returns `Ok(p.c0())`. So all honest parties agree on the
shared secret. -/
theorem honest_shares_recover_same_secret (hS : S.Valid) (hA : Contracts S A)
    (hSh : Shamir.Contracts A.Sh) {corrupt : Finset Party}
    (hcorrupt : S.weightOf corrupt ≤ S.f) {m : A.Message} {signers : Finset Party}
    (hcert : Certificate S A corrupt m signers) {σ : ℕ → State A}
    (hrun : BasicRun A m corrupt σ) (i₀ : Party) :
    ∃ p, ∀ es : List (Shamir.Eval A.F),
      (∀ e ∈ es, ∃ i n o, i ∉ corrupt ∧ (σ n).output i = some o ∧
        e ∈ A.shareList (A.shares o)) →
      (es.map (·.index)).Nodup → es.length = S.t →
      A.Sh.recoverC0 S.t es = .ok (A.Sh.c0 p) := by
  obtain ⟨p, hdeg, hagree⟩ := honest_outputs_agree hS hA hcorrupt hcert hrun i₀
  refine ⟨p, fun es hes hnodup hlen => ?_⟩
  -- Every honest share is `p` evaluated at its own index.
  have heval : es = (es.map (·.index)).map (A.Sh.eval p) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id es]
    refine List.map_congr_left fun e he => ?_
    obtain ⟨i, n, o, hi, ho, hmem⟩ := hes e he
    rw [hagree i n o hi ho, List.mem_map] at hmem
    obtain ⟨k, _, rfl⟩ := hmem
    simp only [id, Function.comp_apply, hSh.eval_index]
  rw [heval]
  exact hSh.recover_c0 S.t p _ hdeg hnodup (by rw [List.length_map, hlen])

end FastcryptoSpecs.Avss
