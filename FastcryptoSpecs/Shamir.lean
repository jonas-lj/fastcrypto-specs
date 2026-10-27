/-
Shamir secret sharing, as implemented by `Poly` in fastcrypto-tbls/src/polynomial.rs.

The functions are black boxes with the names and inputs/outputs of the Rust API. `Contracts`
states what we expect from them, only by relating them to each other; each contract should be
backed by a test against the Rust code. The theorems are proved from the contracts alone.
-/
import Mathlib

namespace FastcryptoSpecs.Shamir

/-- `types::ShareIndex = NonZeroU16`. -/
abbrev ShareIndex := { i : ℕ // 0 < i ∧ i < 2 ^ 16 }

/-- `polynomial::Eval<C>`: a share, i.e. an evaluation at a share index. -/
@[ext]
structure Eval (F : Type) where
  index : ShareIndex
  value : F

/-- `FastCryptoError`, as far as it matters here. -/
inductive Error where
  | invalidInput

/-- The scalar-polynomial API of `Poly<S>` in polynomial.rs. -/
structure Api (F : Type) where
  /-- `Poly<S>`. -/
  Poly : Type
  /-- `Poly::c0`: the constant term, i.e. the shared secret. -/
  c0 : Poly → F
  /-- `Poly::degree_bound`. -/
  degreeBound : Poly → ℕ
  /-- `Poly::rand_fixed_c0(degree, c0, rng)`: the distribution of the polynomial it returns. -/
  randFixedC0 : (degree : ℕ) → (c0 : F) → PMF Poly
  /-- `Poly::eval`. -/
  eval : Poly → ShareIndex → Eval F
  /-- `impl Add<&Poly<C>> for Poly<C>` (via `AddAssign`). -/
  add : Poly → Poly → Poly
  /-- `Poly::recover_c0(t, shares)`. -/
  recoverC0 : (t : ℕ) → List (Eval F) → Except Error F

variable {F : Type} [Field F]

/-- What we expect from the Rust functions. Each field is a property of one or two functions,
to be checked by a test against fastcrypto. -/
structure Contracts (A : Api F) : Prop where
  /-- `rand_fixed_c0(d, s)` has constant term `s`. -/
  rand_c0 : ∀ d s p, p ∈ (A.randFixedC0 d s).support → A.c0 p = s
  /-- `rand_fixed_c0(d, s)` has degree bound `d`. -/
  rand_degree : ∀ d s p, p ∈ (A.randFixedC0 d s).support → A.degreeBound p = d
  /-- `eval(i)` returns a share with index `i`. -/
  eval_index : ∀ p i, (A.eval p i).index = i
  /-- Adding polynomials adds their shares. -/
  add_eval : ∀ p q i, (A.eval (A.add p q) i).value = (A.eval p i).value + (A.eval q i).value
  /-- Adding polynomials adds their constant terms. -/
  add_c0 : ∀ p q, A.c0 (A.add p q) = A.c0 p + A.c0 q
  /-- Adding polynomials gives the larger degree bound. -/
  add_degree : ∀ p q, A.degreeBound (A.add p q) = max (A.degreeBound p) (A.degreeBound q)
  /-- `recover_c0(t, shares)` returns the constant term of a polynomial of degree bound below `t`
  from exactly `t` of its shares at distinct indices. -/
  recover_c0 : ∀ t p (idx : List ShareIndex), A.degreeBound p < t → idx.Nodup →
    idx.length = t → A.recoverC0 t (idx.map (A.eval p)) = .ok (A.c0 p)
  /-- `rand_fixed_c0(d, s)` samples the non-constant coefficients uniformly: adding a fixed
  polynomial `q` of degree bound at most `d` gives the distribution of `rand_fixed_c0(d, s + q.c0())`.
  This is an assumption about the randomness (`S::rand` is uniform), not a unit-testable property. -/
  rand_shift : ∀ d s q, A.degreeBound q ≤ d →
    (A.randFixedC0 d s).map (fun p => A.add p q) = A.randFixedC0 d (s + A.c0 q)
  /-- For fewer than `t` indices and any `c`, some polynomial of degree bound at most `t - 1` has
  constant term `c` and is zero at those indices (e.g. `c · ∏ₖ (1 - x / iₖ)`). -/
  vanishing_exists : ∀ (t : ℕ) (c : F) (idx : List ShareIndex), idx.length < t →
    ∃ q, A.degreeBound q ≤ t - 1 ∧ A.c0 q = c ∧ ∀ i ∈ idx, (A.eval q i).value = 0

variable {A : Api F}

/-- **Dealing.** Shares of a secret `s`, dealt with `rand_fixed_c0(t - 1, s)`: any `t` of them
recover `s`. -/
theorem recover_dealt_secret (hA : Contracts A) {t : ℕ} (ht : 0 < t) {s : F} {p : A.Poly}
    (hp : p ∈ (A.randFixedC0 (t - 1) s).support) (idx : List ShareIndex) (hnodup : idx.Nodup)
    (hlen : idx.length = t) :
    A.recoverC0 t (idx.map (A.eval p)) = .ok s := by
  rw [hA.recover_c0 t p idx (by rw [hA.rand_degree _ _ _ hp]; omega) hnodup hlen,
    hA.rand_c0 _ _ _ hp]

/-- **Agreement.** Any two sets of `t` shares of the same dealing recover the same secret. -/
theorem recover_agrees (hA : Contracts A) {t : ℕ} (ht : 0 < t) {s : F} {p : A.Poly}
    (hp : p ∈ (A.randFixedC0 (t - 1) s).support) (idx idx' : List ShareIndex)
    (h : idx.Nodup ∧ idx.length = t) (h' : idx'.Nodup ∧ idx'.length = t) :
    A.recoverC0 t (idx.map (A.eval p)) = A.recoverC0 t (idx'.map (A.eval p)) := by
  rw [recover_dealt_secret hA ht hp idx h.1 h.2, recover_dealt_secret hA ht hp idx' h'.1 h'.2]

/-- **Privacy.** The shares at fewer than `t` indices have the same distribution for every
secret: they reveal nothing about it. -/
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

/-- The sum of the dealers' polynomials, `p₀ + p₁ + ⋯`, as computed with `add`. -/
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

/-- **DKG.** Every dealer `k` deals a secret `sₖ` with `rand_fixed_c0(t - 1, sₖ)`. Each party adds
up the shares it got from all dealers. Then any `t` of the summed shares recover `Σₖ sₖ`. -/
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
