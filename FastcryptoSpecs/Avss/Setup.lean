/-
Parties, weights and thresholds, as in `threshold_schnorr::Parameters` and `nodes::Nodes`.
-/
import Mathlib

namespace FastcryptoSpecs.Avss

/-- The weights of `Nodes` and the thresholds of `Parameters`
(fastcrypto-tbls/src/threshold_schnorr/mod.rs). -/
structure Setup (Party : Type) where
  /-- Weight of each party (number of shares it holds). -/
  weight : Party → ℕ
  /-- Signing threshold `t`: `t` shares determine the secret. -/
  t : ℕ
  /-- Maximum Byzantine weight `f`. -/
  f : ℕ

namespace Setup

variable {Party : Type}

/-- Total weight of a set of parties (`Nodes::total_weight_of`). -/
def weightOf (S : Setup Party) (A : Finset Party) : ℕ := ∑ i ∈ A, S.weight i

/-- The checks of `Parameters::validate`: `t < W`, `t > f` and `t + f ≤ W`. -/
structure Valid [Fintype Party] (S : Setup Party) : Prop where
  t_lt_W : S.t < ∑ i, S.weight i
  f_lt_t : S.f < S.t
  t_add_f_le_W : S.t + S.f ≤ ∑ i, S.weight i

lemma weightOf_mono (S : Setup Party) {A B : Finset Party} (h : A ⊆ B) :
    S.weightOf A ≤ S.weightOf B :=
  Finset.sum_le_sum_of_subset h

/-- A certificate signed by weight at least `t + f`, with Byzantine weight at most `f`, has
honest signers of weight at least `t` (the argument in `Dealer::create_message`'s docs). -/
lemma honest_signers_weight [DecidableEq Party] (S : Setup Party) (signers corrupt : Finset Party)
    (hcert : S.t + S.f ≤ S.weightOf signers) (hcorrupt : S.weightOf corrupt ≤ S.f) :
    S.t ≤ S.weightOf (signers.filter (· ∉ corrupt)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not signers (· ∈ corrupt) S.weight
  have hsub : S.weightOf (signers.filter (· ∈ corrupt)) ≤ S.weightOf corrupt :=
    S.weightOf_mono (fun x hx => (Finset.mem_filter.mp hx).2)
  unfold weightOf at *
  omega

end Setup

end FastcryptoSpecs.Avss
