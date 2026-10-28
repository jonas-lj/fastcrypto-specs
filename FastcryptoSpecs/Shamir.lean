/-
# Shamir secret sharing

Specification of Shamir secret sharing as implemented by `Poly<S>` in
`fastcrypto-tbls/src/polynomial.rs`.

`Api` lists the Rust functions as black boxes. `Contracts` states what we expect from them. The
theorems are proved from `Contracts` alone.
-/
import Mathlib

namespace FastcryptoSpecs.Shamir

/-- `fastcrypto_tbls::types::ShareIndex` (`NonZeroU16`): a natural number in `[1, 2^16)`. -/
abbrev ShareIndex := { i : ℕ // 0 < i ∧ i < 2 ^ 16 }

/-- `fastcrypto_tbls::polynomial::Eval`: a share, i.e. a value together with the share index it
belongs to. -/
@[ext]
structure Eval (F : Type) where
  index : ShareIndex
  value : F

/-- `FastCryptoError`, as far as it matters here. -/
inductive Error where
  | invalidInput

/-- The scalar-polynomial API of `Poly<S>` in polynomial.rs, as black boxes over the scalar field
`F`, with the names and inputs/outputs of the Rust functions and no implementation.

The functions are total and pure. Field arithmetic is exact. -/
structure Api (F : Type) where
  /-- `fastcrypto_tbls::polynomial::Poly`, for scalars. -/
  Poly : Type
  /-- `fastcrypto_tbls::polynomial::Poly::c0`: the constant term, i.e. the shared secret. -/
  c0 : Poly → F
  /-- `fastcrypto_tbls::polynomial::Poly::degree_bound`: the length of the coefficient vector minus
  one. -/
  degreeBound : Poly → ℕ
  /-- `fastcrypto_tbls::polynomial::Poly::rand_fixed_c0`: the distribution of the polynomial it
  returns, over the randomness of `rng`. "`p` can be returned" means
  `p ∈ (randFixedC0 d s).support`. -/
  randFixedC0 : (degree : ℕ) → (c0 : F) → PMF Poly
  /-- `fastcrypto_tbls::polynomial::Poly::eval`. -/
  eval : Poly → ShareIndex → Eval F
  /-- `fastcrypto_tbls::polynomial::Poly::add` (`impl Add<&Poly<C>> for Poly<C>`). -/
  add : Poly → Poly → Poly
  /-- `fastcrypto_tbls::polynomial::Poly::recover_c0`. `Err` is `.error`; a panic cannot be
  represented, so a contract saying it returns `.ok` also claims that it does not panic on those
  inputs. -/
  recoverC0 : (t : ℕ) → List (Eval F) → Except Error F

variable {F : Type} [Field F]

/-- What we expect from the Rust functions. -/
structure Contracts (A : Api F) : Prop where
  /-- `rand_fixed_c0(d, s).c0() = s` for all `d`, `s`. -/
  rand_c0 : ∀ d s p, p ∈ (A.randFixedC0 d s).support → A.c0 p = s
  /-- `rand_fixed_c0(d, s).degree_bound() = d` for all `d`, `s`. -/
  rand_degree : ∀ d s p, p ∈ (A.randFixedC0 d s).support → A.degreeBound p = d
  /-- `p.eval(i).index = i`. -/
  eval_index : ∀ p i, (A.eval p i).index = i
  /-- `(p + q).eval(i) = p.eval(i) + q.eval(i)`, also when `p` and `q` have different degrees. -/
  add_eval : ∀ p q i, (A.eval (A.add p q) i).value = (A.eval p i).value + (A.eval q i).value
  /-- `(p + q).c0() = p.c0() + q.c0()`. -/
  add_c0 : ∀ p q, A.c0 (A.add p q) = A.c0 p + A.c0 q
  /-- `(p + q).degree_bound() = max(p.degree_bound(), q.degree_bound())`. -/
  add_degree : ∀ p q, A.degreeBound (A.add p q) = max (A.degreeBound p) (A.degreeBound q)
  /-- `recover_c0(t, [p.eval(i₁), …, p.eval(iₜ)]) = Ok(p.c0())` if `p.degree_bound() < t` and
  `i₁, …, iₜ` are distinct. -/
  recover_c0 : ∀ t p (idx : List ShareIndex), A.degreeBound p < t → idx.Nodup →
    idx.length = t → A.recoverC0 t (idx.map (A.eval p)) = .ok (A.c0 p)
  /-- `rand_fixed_c0(d, s) + q` and `rand_fixed_c0(d, s + q.c0())` have the same distribution if
  `q.degree_bound() ≤ d`. -/
  rand_shift : ∀ d s q, A.degreeBound q ≤ d →
    (A.randFixedC0 d s).map (fun p => A.add p q) = A.randFixedC0 d (s + A.c0 q)
  /-- For any `c` and `i₁, …, iₖ` with `k < t`, there is a `q` with `q.degree_bound() ≤ t - 1`,
  `q.c0() = c` and `q.eval(iⱼ) = 0` for all `j`. -/
  vanishing_exists : ∀ (t : ℕ) (c : F) (idx : List ShareIndex), idx.length < t →
    ∃ q, A.degreeBound q ≤ t - 1 ∧ A.c0 q = c ∧ ∀ i ∈ idx, (A.eval q i).value = 0

variable {A : Api F}

/-- **Dealing.** Let `t > 0` and let `p` be a polynomial that `rand_fixed_c0(t - 1, s)` can
return. For every list `idx` of exactly `t` distinct share indices, `recover_c0` on the shares
`p.eval(i)` for `i` in `idx` returns `Ok(s)`. -/
theorem recover_dealt_secret (hA : Contracts A) {t : ℕ} (ht : 0 < t) {s : F} {p : A.Poly}
    (hp : p ∈ (A.randFixedC0 (t - 1) s).support) (idx : List ShareIndex) (hnodup : idx.Nodup)
    (hlen : idx.length = t) :
    A.recoverC0 t (idx.map (A.eval p)) = .ok s := by
  rw [hA.recover_c0 t p idx (by rw [hA.rand_degree _ _ _ hp]; omega) hnodup hlen,
    hA.rand_c0 _ _ _ hp]

/-- **Agreement.** Under the hypotheses of `recover_dealt_secret`, any two lists `idx` and `idx'`
of exactly `t` distinct share indices give the same result of `recover_c0`. -/
theorem recover_agrees (hA : Contracts A) {t : ℕ} (ht : 0 < t) {s : F} {p : A.Poly}
    (hp : p ∈ (A.randFixedC0 (t - 1) s).support) (idx idx' : List ShareIndex)
    (h : idx.Nodup ∧ idx.length = t) (h' : idx'.Nodup ∧ idx'.length = t) :
    A.recoverC0 t (idx.map (A.eval p)) = A.recoverC0 t (idx'.map (A.eval p)) := by
  rw [recover_dealt_secret hA ht hp idx h.1 h.2, recover_dealt_secret hA ht hp idx' h'.1 h'.2]

/-- **Privacy.** For every list `idx` of fewer than `t` share indices and any two secrets `s`,
`s'`: the joint distribution of the shares at `idx` of `rand_fixed_c0(t - 1, s)` equals that of
`rand_fixed_c0(t - 1, s')`. So fewer than `t` shares reveal nothing about the secret
(information-theoretically). -/
theorem shares_independent_of_secret (hA : Contracts A) {t : ℕ} (s s' : F)
    (idx : List ShareIndex) (hlen : idx.length < t) :
    (A.randFixedC0 (t - 1) s).map (fun p => idx.map (A.eval p)) =
      (A.randFixedC0 (t - 1) s').map (fun p => idx.map (A.eval p)) := by
  -- Shift the dealing of `s` by a polynomial with constant term `s' - s` that is zero at `idx`:
  -- this gives the dealing of `s'` and leaves the shares at `idx` unchanged.
  obtain ⟨q, hqdeg, hqc0, hqzero⟩ := hA.vanishing_exists t (s' - s) idx hlen
  have hshift := hA.rand_shift (t - 1) s q hqdeg
  have hs : s + (s' - s) = s' := by ring
  rw [hqc0, hs] at hshift
  rw [← hshift, PMF.map_comp]
  congr 1
  funext p
  refine List.map_congr_left fun i hi => ?_
  ext
  · rw [hA.eval_index, hA.eval_index]
  · rw [hA.add_eval, hqzero i hi, add_zero]

/-! ### Summing dealings (the core of `complete_dkg`) -/

/-- The sum `p₀ + p₁ + ⋯` of the dealers' polynomials, computed left to right with `add`. -/
def sumPolys (A : Api F) (p : A.Poly) (rest : List A.Poly) : A.Poly :=
  rest.foldl A.add p

lemma sumPolys_eval {A : Api F} (hadd : ∀ p q i,
    (A.eval (A.add p q) i).value = (A.eval p i).value + (A.eval q i).value)
    (p : A.Poly) (rest : List A.Poly) (i : ShareIndex) :
    (A.eval (sumPolys A p rest) i).value =
      (A.eval p i).value + (rest.map (fun q => (A.eval q i).value)).sum := by
  induction rest generalizing p with
  | nil => simp [sumPolys]
  | cons q rest ih =>
    simp only [sumPolys, List.foldl_cons] at ih ⊢
    rw [ih, hadd, List.map_cons, List.sum_cons, add_assoc]

lemma sumPolys_c0 (hA : Contracts A) (p : A.Poly) (rest : List A.Poly) :
    A.c0 (sumPolys A p rest) = A.c0 p + (rest.map A.c0).sum := by
  induction rest generalizing p with
  | nil => simp [sumPolys]
  | cons q rest ih =>
    simp only [sumPolys, List.foldl_cons] at ih ⊢
    rw [ih, hA.add_c0, List.map_cons, List.sum_cons, add_assoc]

lemma sumPolys_degree (hA : Contracts A) {d : ℕ} (p : A.Poly) (rest : List A.Poly)
    (hp : A.degreeBound p = d) (hrest : ∀ q ∈ rest, A.degreeBound q = d) :
    A.degreeBound (sumPolys A p rest) = d := by
  induction rest generalizing p with
  | nil => simpa [sumPolys]
  | cons q rest ih =>
    simp only [sumPolys, List.foldl_cons] at ih ⊢
    apply ih
    · rw [hA.add_degree, hp, hrest q List.mem_cons_self, max_self]
    · exact fun q' hq' => hrest q' (List.mem_cons_of_mem _ hq')

/-- **DKG.** Let `t > 0` and let `dealings` be a nonempty list of pairs `(sₖ, pₖ)`, where each
`pₖ` is a polynomial that `rand_fixed_c0(t - 1, sₖ)` can return. For every list `idx` of exactly
`t` distinct share indices, `recover_c0` on the summed shares `Σₖ pₖ.eval(i).value` (one per `i` in
`idx`, with index `i`) returns `Ok(Σₖ sₖ)`. -/
theorem recover_sum_of_dealings (hA : Contracts A) {t : ℕ} (ht : 0 < t)
    (dealings : List (F × A.Poly)) (hne : dealings ≠ [])
    (hdealt : ∀ d ∈ dealings, d.2 ∈ (A.randFixedC0 (t - 1) d.1).support)
    (idx : List ShareIndex) (hnodup : idx.Nodup) (hlen : idx.length = t) :
    A.recoverC0 t (idx.map fun i =>
        ⟨i, (dealings.map fun d => (A.eval d.2 i).value).sum⟩) =
      .ok (dealings.map Prod.fst).sum := by
  obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  let P := sumPolys A d.2 (rest.map Prod.snd)
  -- The summed shares are the shares of the summed polynomial.
  have hshares : (idx.map fun i =>
      (⟨i, ((d :: rest).map fun d => (A.eval d.2 i).value).sum⟩ : Eval F)) =
      idx.map (A.eval P) := by
    refine List.map_congr_left fun i _ => ?_
    ext
    · rw [hA.eval_index]
    · simp only [P, sumPolys_eval hA.add_eval, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def]
  have hdeg : A.degreeBound P = t - 1 :=
    sumPolys_degree hA _ _ (hA.rand_degree _ _ _ (hdealt d List.mem_cons_self))
      (fun q hq => by
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hq
        exact hA.rand_degree _ _ _ (hdealt d' (List.mem_cons_of_mem _ hd')))
  have hc0 : A.c0 P = ((d :: rest).map Prod.fst).sum := by
    simp only [P, sumPolys_c0 hA, List.map_map, List.map_cons, List.sum_cons]
    rw [hA.rand_c0 _ _ _ (hdealt d List.mem_cons_self)]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun d' hd' => ?_)
    exact hA.rand_c0 _ _ _ (hdealt d' (List.mem_cons_of_mem _ hd'))
  rw [hshares, hA.recover_c0 t P idx (by omega) hnodup hlen, hc0]

end FastcryptoSpecs.Shamir
