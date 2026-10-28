/-
A toy implementation of the Shamir API that satisfies `Shamir.Contracts`, so the contracts are
consistent.
-/
import FastcryptoSpecs.Shamir

namespace FastcryptoSpecs.NonVacuity

open Polynomial FastcryptoSpecs.Shamir

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- The scalar field: `ZMod 65537`, a prime field larger than every share index. -/
abbrev F := ZMod 65537

/-- A polynomial over `F` together with a bound on its degree, like `Poly<S>` with its coefficient
vector. -/
structure TPoly where
  bound : ℕ
  poly : F[X]
  coeff_zero : ∀ m, bound < m → poly.coeff m = 0

lemma TPoly.ext' {p q : TPoly} (h1 : p.bound = q.bound) (h2 : p.poly = q.poly) : p = q := by
  cases p; cases q; cases h1; cases h2; rfl

lemma TPoly.degree_lt (p : TPoly) {t : ℕ} (h : p.bound < t) : p.poly.degree < t :=
  degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm => p.coeff_zero m (by omega)

/-- A share index as a field element. -/
def idxF (i : ShareIndex) : F := (i.1 : F)

lemma idxF_injective : Function.Injective idxF := by
  intro i j h
  have h' := (ZMod.natCast_eq_natCast_iff' i.1 j.1 65537).mp h
  rw [Nat.mod_eq_of_lt (by have := i.2.2; omega), Nat.mod_eq_of_lt (by have := j.2.2; omega)] at h'
  exact Subtype.ext h'

lemma idxF_ne_zero (i : ShareIndex) : idxF i ≠ 0 := by
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' i.1 0 65537).mp (by simpa [idxF] using h)
  rw [Nat.mod_eq_of_lt (by have := i.2.2; omega)] at h'
  have := i.2.1
  simp at h'
  omega

/-- The polynomial `s + X·r`, where the coefficients of `r` are `v`. -/
noncomputable def sample (d : ℕ) (s : F) (v : Fin d → F) : TPoly where
  bound := d
  poly := C s + X * ((degreeLTEquiv F d).symm v : F[X])
  coeff_zero m hm := by
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hr := mem_degreeLT.mp ((degreeLTEquiv F d).symm v).2
    rw [coeff_add, coeff_C, if_neg (by omega), coeff_X_mul, zero_add]
    exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr (by exact_mod_cast (by omega : d ≤ m)))

open Classical in
/-- Interpolation: the constant term of a polynomial of degree below `t` through the shares, if
there is one. -/
noncomputable def recover (t : ℕ) (es : List (Eval F)) : Except Error F :=
  if h : ∃ f : F[X], f.degree < t ∧ ∀ e ∈ es, f.eval (idxF e.index) = e.value then
    .ok ((Classical.choose h).eval 0)
  else .error .invalidInput

/-- Constant term. -/
noncomputable def tc0 (p : TPoly) : F := p.poly.eval 0

/-- Sum of two polynomials; the degree bound is the larger one. -/
noncomputable def tadd (p q : TPoly) : TPoly :=
  ⟨max p.bound q.bound, p.poly + q.poly, fun m hm => by
    rw [coeff_add, p.coeff_zero m (by omega), q.coeff_zero m (by omega), add_zero]⟩

/-- The toy Shamir API. -/
noncomputable def toyShamir : Api F where
  Poly := TPoly
  c0 := tc0
  degreeBound p := p.bound
  randFixedC0 d s := (PMF.uniformOfFintype (Fin d → F)).map (sample d s)
  eval p i := ⟨i, p.poly.eval (idxF i)⟩
  add := tadd
  recoverC0 := recover

lemma map_uniform_equiv {α : Type} [Fintype α] [Nonempty α] (e : α ≃ α) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype α := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    rw [if_neg]
    rintro rfl
    exact ha (e.symm_apply_apply a).symm

lemma toy_recover_c0 (t : ℕ) (p : TPoly) (idx : List ShareIndex) (hdeg : p.bound < t)
    (hnodup : idx.Nodup) (hlen : idx.length = t) :
    toyShamir.recoverC0 t (idx.map (toyShamir.eval p)) = .ok (toyShamir.c0 p) := by
  have hex : ∃ f : F[X], f.degree < t ∧
      ∀ e ∈ idx.map (toyShamir.eval p), f.eval (idxF e.index) = e.value := by
    refine ⟨p.poly, p.degree_lt hdeg, fun e he => ?_⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    rfl
  show recover t (idx.map (toyShamir.eval p)) = _
  rw [recover, dif_pos hex]
  obtain ⟨hgdeg, hgeval⟩ := Classical.choose_spec hex
  set s := (idx.map idxF).toFinset
  have hs : s.card = t := by
    rw [List.toFinset_card_of_nodup (hnodup.map idxF_injective), List.length_map, hlen]
  have hg : Classical.choose hex = p.poly := by
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq s (by rwa [hs]) (by rw [hs]; exact p.degree_lt hdeg)
      fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hgeval _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  rw [hg]
  rfl

lemma toy_rand_shift (d : ℕ) (s : F) (q : TPoly) (hq : q.bound ≤ d) :
    ((PMF.uniformOfFintype (Fin d → F)).map (sample d s)).map (fun p => tadd p q) =
      (PMF.uniformOfFintype (Fin d → F)).map (sample d (s + tc0 q)) := by
  -- `q = q(0) + X·divX(q)`, and `divX(q)` has degree below `d`.
  have hdiv : divX q.poly ∈ degreeLT F d := mem_degreeLT.mpr <|
    degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm => by
      rw [coeff_divX]; exact q.coeff_zero _ (by omega)
  set w := degreeLTEquiv F d ⟨divX q.poly, hdiv⟩
  have hstep : ∀ v, tadd (sample d s v) q = sample d (s + tc0 q) (v + w) := by
    intro v
    apply TPoly.ext'
    · exact max_eq_left hq
    · show C s + X * _ + q.poly = C (s + q.poly.eval 0) + X * _
      rw [show (degreeLTEquiv F d).symm (v + w) =
          (degreeLTEquiv F d).symm v + ⟨divX q.poly, hdiv⟩ by
        rw [map_add, LinearEquiv.symm_apply_apply], Submodule.coe_add]
      conv_lhs => rw [← X_mul_divX_add q.poly]
      rw [← coeff_zero_eq_eval_zero, C_add]
      ring
  have hcomp : (fun p => tadd p q) ∘ sample d s = sample d (s + tc0 q) ∘ Equiv.addRight w :=
    funext hstep
  rw [PMF.map_comp, hcomp, ← PMF.map_comp, map_uniform_equiv]

lemma toy_vanishing (t : ℕ) (c : F) (idx : List ShareIndex) (hlen : idx.length < t) :
    ∃ q : TPoly, q.bound ≤ t - 1 ∧ toyShamir.c0 q = c ∧
      ∀ i ∈ idx, (toyShamir.eval q i).value = 0 := by
  set P : F[X] := (idx.map fun i => X - C (idxF i)).prod
  have hP0 : P.eval 0 ≠ 0 := by
    rw [eval_list_prod, List.map_map]
    refine List.prod_ne_zero fun h => ?_
    obtain ⟨i, _, hi⟩ := List.mem_map.mp h
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub, neg_eq_zero] at hi
    exact idxF_ne_zero i hi
  have hPdeg : P.natDegree ≤ idx.length := by
    refine (natDegree_list_prod_le _).trans (le_of_eq ?_)
    simp [Function.comp_def]
  refine ⟨⟨t - 1, C (c * (P.eval 0)⁻¹) * P, fun m hm => ?_⟩, le_rfl, ?_, fun i hi => ?_⟩
  · exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_C_mul_le _ _).trans_lt (by omega))
  · show (C (c * (P.eval 0)⁻¹) * P).eval 0 = c
    rw [eval_mul, eval_C, mul_assoc, inv_mul_cancel₀ hP0, mul_one]
  · show (C (c * (P.eval 0)⁻¹) * P).eval (idxF i) = 0
    rw [eval_mul]
    apply mul_eq_zero_of_right
    simp only [P]
    rw [eval_list_prod, List.map_map]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨i, hi, by simp⟩)

/-- The toy Shamir API satisfies all Shamir contracts. -/
theorem toyShamir_contracts : Contracts toyShamir where
  rand_c0 d s p hp := by
    obtain ⟨v, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    show (C s + X * _).eval 0 = s
    simp
  rand_degree d s p hp := by
    obtain ⟨v, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    rfl
  eval_index p i := rfl
  add_eval p q i := eval_add
  add_c0 p q := eval_add
  add_degree p q := rfl
  recover_c0 := toy_recover_c0
  rand_shift := toy_rand_shift
  vanishing_exists := toy_vanishing

end FastcryptoSpecs.NonVacuity
