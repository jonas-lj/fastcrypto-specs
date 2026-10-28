/-
DKG from AVSS: every honest party combines the outputs of the same certified dealers with
`AvssOutput::complete_dkg`, and the combined shares are shares of the sum of the dealers' secrets.
-/
import FastcryptoSpecs.Avss.Agreement

namespace FastcryptoSpecs.Avss

/-- `AvssOutput::complete_dkg` and `DkOutput` as black boxes.

One `Api` covers the AVSS instances of all dealers. Its contracts quantify over all messages, so
they apply to each instance; each instance has its own session id, on which its receivers agree. -/
structure DkgApi (Party : Type) (A : Api Party) where
  /-- `avss::DkOutput`. -/
  DkOutput : Type
  /-- `AvssOutput::complete_dkg(t, nodes, outputs)`, with the map `outputs` from dealer id to that
  dealer's `AvssOutput` given as a list of pairs. `none` is an `Err`. -/
  completeDkg : List (Party × A.Output) → Option DkOutput
  /-- The `my_shares` field of `DkOutput`. -/
  shares : DkOutput → A.Shares

variable {Party : Type} [DecidableEq Party]

/-- What we expect from `complete_dkg`. -/
structure DkgContracts (S : Setup Party) (A : Api Party) (D : DkgApi Party A) : Prop where
  /-- `complete_dkg(os) = Ok(dk)` and each `o ∈ os` holds the shares `[(k, v_o(k)) for k in idx]`
  ⇒ `dk.my_shares = [(k, Σ_{o ∈ os} v_o(k)) for k in idx]`. -/
  complete_sum : ∀ os dk (idx : List Shamir.ShareIndex)
      (v : Party × A.Output → Shamir.ShareIndex → A.F),
    D.completeDkg os = some dk →
    (∀ o ∈ os, A.shareList (A.shares o.2) = idx.map fun k => (⟨k, v o k⟩ : Shamir.Eval A.F)) →
    A.shareList (D.shares dk) =
      idx.map fun k => (⟨k, (os.map fun o => v o k).sum⟩ : Shamir.Eval A.F)
  /-- `os` is nonempty, its dealers are distinct with total weight `≥ t`, and each `o ∈ os` holds
  shares at the indices `idx` ⇒ `complete_dkg(os) = Ok(dk)` for some `dk`. -/
  complete_ok : ∀ os (idx : List Shamir.ShareIndex), os ≠ [] → (os.map Prod.fst).Nodup →
    S.t ≤ S.weightOf (os.map Prod.fst).toFinset →
    (∀ o ∈ os, (A.shareList (A.shares o.2)).map (·.index) = idx) →
    ∃ dk, D.completeDkg os = some dk

variable [Fintype Party] {S : Setup Party} {A : Api Party} {D : DkgApi Party A}

/-- The input party `i` passes to `complete_dkg`: the output it holds from each dealer in
`dealers`. -/
def dkgInput (dealers : List Party) (out : Party → Party → A.Output) (i : Party) :
    List (Party × A.Output) :=
  dealers.map fun d => (d, out i d)

omit [DecidableEq Party] [Fintype Party] in
lemma dkgInput_fst (dealers : List Party) (out : Party → Party → A.Output) (i : Party) :
    (dkgInput dealers out i).map Prod.fst = dealers := by
  simp [dkgInput, Function.comp_def]

/-- Per dealer, a polynomial of degree below `t` that every honest output fits. -/
lemma dealer_polys (hS : S.Valid) (hA : Contracts S A) {corrupt : Finset Party}
    (hcorrupt : S.Tolerates corrupt) {dealers : List Party} (hne : dealers ≠ [])
    {m : Party → A.Message} {signers : Party → Finset Party}
    (hcert : ∀ d ∈ dealers, Certificate S A corrupt (m d) (signers d))
    {σ : Party → ℕ → State A} (hrun : ∀ d ∈ dealers, BasicRun A (m d) corrupt (σ d)) :
    ∃ p : Party → A.Sh.Poly, ∀ d ∈ dealers, A.Sh.degreeBound (p d) < S.t ∧
      ∀ i n o, i ∉ corrupt → (σ d n).output i = some o →
        A.shareList (A.shares o) = (A.shareIds i).map (A.Sh.eval (p d)) := by
  have h : ∀ d ∈ dealers, ∃ p, A.Sh.degreeBound p < S.t ∧
      ∀ i n o, i ∉ corrupt → (σ d n).output i = some o →
        A.shareList (A.shares o) = (A.shareIds i).map (A.Sh.eval p) :=
    fun d hd => honest_outputs_agree hS hA hcorrupt (hcert d hd) (hrun d hd) d
  obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil dealers hne
  haveI : Nonempty A.Sh.Poly := ⟨(h d₀ hd₀).choose⟩
  choose! p hp using h
  exact ⟨p, hp⟩

/-- **DKG completes.** Let `dealers` be nonempty, without repeats and of total weight `≥ t`, and
suppose that for each dealer `d` in it, every honest party `i` holds the output `out i d` of `d`'s
instance at some time (caller obligation). Then `complete_dkg` returns `Ok` for every honest party
`i` on `dkgInput dealers out i`. -/
theorem dkg_completes (hS : S.Valid) (hA : Contracts S A) (hSh : Shamir.Contracts A.Sh)
    (hD : DkgContracts S A D) {corrupt : Finset Party} (hcorrupt : S.Tolerates corrupt)
    {dealers : List Party} {m : Party → A.Message} {signers : Party → Finset Party}
    (hcert : ∀ d ∈ dealers, Certificate S A corrupt (m d) (signers d))
    {σ : Party → ℕ → State A} (hrun : ∀ d ∈ dealers, BasicRun A (m d) corrupt (σ d))
    {out : Party → Party → A.Output}
    (hout : ∀ i, i ∉ corrupt → ∀ d ∈ dealers, ∃ n, (σ d n).output i = some (out i d))
    (hne : dealers ≠ []) (hnodup : dealers.Nodup) (hweight : S.t ≤ S.weightOf dealers.toFinset)
    (i : Party) (hi : i ∉ corrupt) :
    ∃ dk, D.completeDkg (dkgInput dealers out i) = some dk := by
  obtain ⟨p, hp⟩ := dealer_polys hS hA hcorrupt hne hcert hrun
  refine hD.complete_ok _ (A.shareIds i) (by simpa [dkgInput] using hne)
    (by rwa [dkgInput_fst]) (by rwa [dkgInput_fst]) ?_
  intro o ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
  obtain ⟨n, hn⟩ := hout i hi d hd
  rw [(hp d hd).2 i n _ hi hn, List.map_map]
  conv_rhs => rw [← List.map_id (A.shareIds i)]
  exact List.map_congr_left fun k _ => hSh.eval_index _ k

/-- **DKG agreement.** Let `dealers` be nonempty, and `out` as in `dkg_completes`. There are
polynomials `p d`, one per dealer `d` in `dealers`, each with `degree_bound() < t`, such that
whenever `complete_dkg` returns `Ok(dk)` for an honest party `i` on `dkgInput dealers out i`,
`dk.my_shares = [(k, Σ_d (p d).eval(k).value) for k in share_ids_of(i)]`.

All honest parties pass the same `dealers`: this is the caller obligation that all parties use the
outputs of the same certified dealers. -/
theorem dkg_outputs_agree (hS : S.Valid) (hA : Contracts S A) (hSh : Shamir.Contracts A.Sh)
    (hD : DkgContracts S A D) {corrupt : Finset Party} (hcorrupt : S.Tolerates corrupt)
    {dealers : List Party} {m : Party → A.Message} {signers : Party → Finset Party}
    (hcert : ∀ d ∈ dealers, Certificate S A corrupt (m d) (signers d))
    {σ : Party → ℕ → State A} (hrun : ∀ d ∈ dealers, BasicRun A (m d) corrupt (σ d))
    {out : Party → Party → A.Output}
    (hout : ∀ i, i ∉ corrupt → ∀ d ∈ dealers, ∃ n, (σ d n).output i = some (out i d))
    (hne : dealers ≠ []) :
    ∃ p : Party → A.Sh.Poly, (∀ d ∈ dealers, A.Sh.degreeBound (p d) < S.t) ∧
      ∀ i dk, i ∉ corrupt → D.completeDkg (dkgInput dealers out i) = some dk →
        A.shareList (D.shares dk) = (A.shareIds i).map fun k =>
          (⟨k, (dealers.map fun d => (A.Sh.eval (p d) k).value).sum⟩ : Shamir.Eval A.F) := by
  obtain ⟨p, hp⟩ := dealer_polys hS hA hcorrupt hne hcert hrun
  refine ⟨p, fun d hd => (hp d hd).1, fun i dk hi hdk => ?_⟩
  have := hD.complete_sum _ dk (A.shareIds i) (fun o k => (A.Sh.eval (p o.1) k).value) hdk
    (fun o ho => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
      obtain ⟨n, hn⟩ := hout i hi d hd
      rw [(hp d hd).2 i n _ hi hn]
      refine List.map_congr_left fun k _ => ?_
      ext
      · simp [hSh.eval_index]
      · rfl)
  rw [this]
  simp [dkgInput, Function.comp_def]

omit [DecidableEq Party] [Fintype Party] in
lemma sumPolys_degree_lt (hSh : Shamir.Contracts A.Sh) {t : ℕ} (p : A.Sh.Poly)
    (rest : List A.Sh.Poly) (hp : A.Sh.degreeBound p < t)
    (hrest : ∀ q ∈ rest, A.Sh.degreeBound q < t) :
    A.Sh.degreeBound (Shamir.sumPolys A.Sh p rest) < t := by
  induction rest generalizing p with
  | nil => simpa [Shamir.sumPolys]
  | cons q rest ih =>
    simp only [Shamir.sumPolys, List.foldl_cons] at ih ⊢
    apply ih
    · rw [hSh.add_degree]
      exact max_lt hp (hrest q List.mem_cons_self)
    · exact fun q' hq' => hrest q' (List.mem_cons_of_mem _ hq')

/-- **DKG: same secret.** Let `dealers` be nonempty, and `out` as in `dkg_completes`. There are
polynomials `p d`, one per dealer `d` in `dealers`, such that `recover_c0(t, es) = Ok(Σ_d
(p d).c0())` for every list `es` of exactly `t` shares at distinct indices, each taken from the
`DkOutput` that `complete_dkg` returned to some honest party. -/
theorem dkg_recover_same_secret (hS : S.Valid) (hA : Contracts S A)
    (hSh : Shamir.Contracts A.Sh) (hD : DkgContracts S A D) {corrupt : Finset Party}
    (hcorrupt : S.Tolerates corrupt) {dealers : List Party} {m : Party → A.Message}
    {signers : Party → Finset Party}
    (hcert : ∀ d ∈ dealers, Certificate S A corrupt (m d) (signers d))
    {σ : Party → ℕ → State A} (hrun : ∀ d ∈ dealers, BasicRun A (m d) corrupt (σ d))
    {out : Party → Party → A.Output}
    (hout : ∀ i, i ∉ corrupt → ∀ d ∈ dealers, ∃ n, (σ d n).output i = some (out i d))
    (hne : dealers ≠ []) :
    ∃ p : Party → A.Sh.Poly, ∀ es : List (Shamir.Eval A.F),
      (∀ e ∈ es, ∃ i dk, i ∉ corrupt ∧ D.completeDkg (dkgInput dealers out i) = some dk ∧
        e ∈ A.shareList (D.shares dk)) →
      (es.map (·.index)).Nodup → es.length = S.t →
      A.Sh.recoverC0 S.t es = .ok (dealers.map fun d => A.Sh.c0 (p d)).sum := by
  obtain ⟨p, hdeg, hagree⟩ :=
    dkg_outputs_agree hS hA hSh hD hcorrupt hcert hrun hout hne
  refine ⟨p, fun es hes hnodup hlen => ?_⟩
  obtain ⟨d₀, rest, hdealers⟩ := List.exists_cons_of_ne_nil hne
  -- The joint polynomial.
  let P := Shamir.sumPolys A.Sh (p d₀) (rest.map p)
  have hP : ∀ k, (A.Sh.eval P k).value = (dealers.map fun d => (A.Sh.eval (p d) k).value).sum := by
    intro k
    simp only [P, Shamir.sumPolys_eval hSh.add_eval, hdealers, List.map_cons, List.sum_cons,
      List.map_map, Function.comp_def]
  -- Every share in `es` is `P` evaluated at its own index.
  have heval : es = (es.map (·.index)).map (A.Sh.eval P) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id es]
    refine List.map_congr_left fun e he => ?_
    obtain ⟨i, dk, hi, hdk, hmem⟩ := hes e he
    rw [hagree i dk hi hdk, List.mem_map] at hmem
    obtain ⟨k, _, rfl⟩ := hmem
    ext
    · simp [hSh.eval_index]
    · simp [hP]
  have hPdeg : A.Sh.degreeBound P < S.t :=
    sumPolys_degree_lt hSh _ _ (hdeg d₀ (by simp [hdealers]))
      (fun q hq => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
        exact hdeg d (by simp [hdealers, hd]))
  have hc0 : A.Sh.c0 P = (dealers.map fun d => A.Sh.c0 (p d)).sum := by
    simp only [P, Shamir.sumPolys_c0 hSh, hdealers, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_def]
  rw [heval, hSh.recover_c0 S.t P _ hPdeg hnodup (by rw [List.length_map, hlen]), hc0]

end FastcryptoSpecs.Avss
