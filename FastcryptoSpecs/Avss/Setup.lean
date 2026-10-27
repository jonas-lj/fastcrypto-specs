/-
Parties, weights and thresholds, as in `threshold_schnorr::Parameters` and `nodes::Nodes`
(fastcrypto-tbls/src/threshold_schnorr/mod.rs, fastcrypto-tbls/src/nodes.rs).
-/
import Mathlib

namespace FastcryptoSpecs.Avss

/-- The node weights of `Nodes` and the thresholds `t`, `f` of `Parameters`. The parties are the
elements of a finite type `Party` (the node ids `0..n` of `Nodes`). -/
structure Setup (Party : Type) where
  /-- Weight of each party: the number of share indices it holds (`Nodes::share_ids_of`). -/
  weight : Party → ℕ
  /-- Threshold `t`: shares at `t` distinct indices determine the secret. -/
  t : ℕ
  /-- Maximum total weight of Byzantine parties, `f`. -/
  f : ℕ

namespace Setup

variable {Party : Type}

/-- Total weight of a set of parties (`Nodes::total_weight_of`). -/
def weightOf (S : Setup Party) (A : Finset Party) : ℕ := ∑ i ∈ A, S.weight i

/-- The checks of `Parameters::validate(W)`, where `W` is the total weight. (`validate` also
rejects `f = 0`; no theorem here needs that.) -/
structure Valid [Fintype Party] (S : Setup Party) : Prop where
  /-- `t < W`. -/
  t_lt_W : S.t < ∑ i, S.weight i
  /-- `f < t`. -/
  f_lt_t : S.f < S.t
  /-- `t + f ≤ W`. -/
  t_add_f_le_W : S.t + S.f ≤ ∑ i, S.weight i

lemma weightOf_mono (S : Setup Party) {A B : Finset Party} (h : A ⊆ B) :
    S.weightOf A ≤ S.weightOf B :=
  Finset.sum_le_sum_of_subset h

/-- If `signers` has weight at least `t + f` and `corrupt` has weight at most `f`, then the
signers outside `corrupt` have weight at least `t` (the argument in the docs of
`Dealer::create_message`). -/
lemma honest_signers_weight [DecidableEq Party] (S : Setup Party) (signers corrupt : Finset Party)
    (hcert : S.t + S.f ≤ S.weightOf signers) (hcorrupt : S.weightOf corrupt ≤ S.f) :
    S.t ≤ S.weightOf (signers.filter (· ∉ corrupt)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not signers (· ∈ corrupt) S.weight
  have hsub : S.weightOf (signers.filter (· ∈ corrupt)) ≤ S.weightOf corrupt :=
    S.weightOf_mono (fun x hx => (Finset.mem_filter.mp hx).2)
  unfold weightOf at *
  omega

/-- The weights of a set and of its complement add up to the total weight `W`. -/
lemma weightOf_add_compl [Fintype Party] [DecidableEq Party] (S : Setup Party)
    (A : Finset Party) : S.weightOf A + S.weightOf Aᶜ = ∑ i, S.weight i :=
  Finset.sum_add_sum_compl A S.weight

end Setup

end FastcryptoSpecs.Avss
