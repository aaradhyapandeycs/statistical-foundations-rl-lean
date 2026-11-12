import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.FixedPointDefinitions
import Formalization.MDP.OptimalityOperatorDefinitions
import Formalization.OfflineRL.LCBQDefinitions

/-! # Printed Lemma 6.11 is false: no universal constant works (SOURCE-ISSUES C22)

Source: `lemma:useful`, `chapters/offlineRL.tex:2292–2300`, with
`H = ⌈4 log(SAT/δ)/(1−γ)⌉` (`eq:defn-H-lcbq-stepsize-proof`, `:1667–1672`) and
`κ = γ(1+1/H)³` (`eq:defn-kappa-proof-lcbq`, `:2284–2289`).

`Lemma6_11_printed` is the statement-index entry `Lemma6_11_restricted`
(`Formalization/Statements/Ch6.lean`) with its added premise `1 ≤ log(SAT/δ)` removed; the
source's `≲` is one universal constant `C > 0`, quantified before everything else.

Instance (C22, second family): `S = A = T = 1`, `δ = 9/10`, `W ≡ 1`, discount
`γ = 3C/(8(3C+1)) = 1/8 − η` with `η = 1/(8(3C+1))`, so `γ ∈ [0, 1/8)`. Then
`0 < 4 log(10/9)/(1−γ) ≤ 32/63`, hence `H = 1` and `κ = 8γ = 1 − 8η < 1`. The occupancies are `1`
(one state), so the left side is `∑ κʲ = 1/(1−κ) = 3C+1`, while the right side is
`C(1 + δ‖W‖)/(1−γ) ≤ C · 1.9 · 8/7 < 2.2 C`.

This family keeps `κ < 1`, so the series converges and the refutation does not use Lean's
convention that the `tsum` of a non-summable series is `0` (the `κ ≥ 1` example of C22,
`γ = 0.3`, is deliberately avoided). Classification: genuine counterexample to the printed
universal-constant claim, located in the corner `log(SAT/δ) < 1` (here `S A T = 1`), not a junk
value. It does not affect Theorem 6.8 (C22, C24).
-/

open scoped BigOperators

namespace StatisticalRL.OfflineRL

universe u v

/-- Printed Lemma 6.11 (`lemma:useful`, `chapters/offlineRL.tex:2292–2300`):
`Lemma6_11_restricted` without the premise `1 ≤ log(SAT/δ)`. -/
def Lemma6_11_printed : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
      (ρ : FiniteDistribution S) (πstar : S → A),
      (∀ s, letI : Nonempty A := M.action_nonempty
        M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s)) →
      ∀ (δ : ℝ) (T : ℕ) (W : S → ℝ),
      0 < δ → δ < 1 → 1 ≤ T →
      (∀ s, 0 ≤ W s) →
      let γ := M.discount
      let H : ℕ := ⌈4 / (1 - γ) * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ)⌉₊
      let κ := γ * (1 + 1 / (H : ℝ)) ^ 3
      ∑' j : ℕ, κ ^ j * ∑ s,
          M.occupancyStateAt (OfflineRL.LCBQ.detPolicy πstar) ρ j s * W s ≤
        C * ((∑ s, M.discountedStateOccupancy (OfflineRL.LCBQ.detPolicy πstar) ρ s * W s) /
            (1 - γ) +
          δ * ‖W‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - γ)))

/-- Every probability vector on the one-point type is `1`. -/
theorem lemma611_unit_prob (d : FiniteDistribution Unit) (x : Unit) : d.prob x = 1 := by
  simpa using d.sum_prob

/-- The probability vector on the one-point type. -/
noncomputable def lemma611UnitDist : FiniteDistribution Unit :=
  FiniteDistribution.ofUnique Unit

/-- One state, one action, reward `0`, discount `γ`. -/
noncomputable def lemma611MDP (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) : DiscountedMDP Unit Unit where
  state_nonempty := ⟨()⟩
  action_nonempty := ⟨()⟩
  transition := fun _ _ ↦ lemma611UnitDist
  reward := fun _ _ ↦ 0
  reward_nonneg := fun _ _ ↦ le_rfl
  reward_le_one := fun _ _ ↦ zero_le_one
  discount := γ
  discount_nonneg := h0
  discount_lt_one := h1

/-- With `γ ≤ 1/8` the printed `H` equals `1` at `S = A = T = 1`, `δ = 9/10`. -/
theorem lemma611_H (γ : ℝ) (h8 : γ ≤ 1 / 8) :
    ⌈4 / (1 - γ) * Real.log (1 / (9 / 10))⌉₊ = 1 := by
  have hl : Real.log (1 / (9 / 10)) = Real.log (10 / 9) := by norm_num
  rw [hl, Nat.ceil_eq_iff one_ne_zero]
  have hpos : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
  have h1γ : 0 < 1 - γ := by linarith
  constructor
  · simp only [tsub_self, CharP.cast_eq_zero]
    positivity
  · rw [Nat.cast_one, div_mul_eq_mul_div, div_le_one h1γ]
    nlinarith

/-- On one state the normalized discounted occupancy is `1`. -/
theorem lemma611_occ (M : DiscountedMDP Unit Unit) (π : StationaryPolicy Unit Unit)
    (ρ : FiniteDistribution Unit) (x : Unit) : M.discountedStateOccupancy π ρ x = 1 := by
  simpa using M.discountedStateOccupancy_sum π ρ

/-- Sup-norm bound, stated for a generic finite carrier so that it uses the same norm instance as
the transcribed statement. -/
theorem lemma611_norm_le {S : Type*} [Fintype S] (W : S → ℝ) (hW : ∀ s, |W s| ≤ 1) :
    ‖W‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun s ↦ by simpa [Real.norm_eq_abs] using hW s

/-- **C22.** Printed Lemma 6.11 is false: for every candidate constant `C > 0` the instance
`S = A = T = 1`, `δ = 9/10`, `W ≡ 1`, `γ = 3C/(8(3C+1))` has left side `3C+1` and right side
below `2.2 C`. -/
theorem not_Lemma6_11_printed : ¬ Lemma6_11_printed.{0, 0} := by
  rintro ⟨C, hC, h⟩
  have hden : 0 < 8 * (3 * C + 1) := by positivity
  set γ : ℝ := 3 * C / (8 * (3 * C + 1)) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hγ8 : γ ≤ 1 / 8 := by rw [hγ, div_le_iff₀ hden]; linarith
  have hγ8' : γ < 1 / 8 := by rw [hγ, div_lt_iff₀ hden]; linarith
  have hγ1 : γ < 1 := by linarith
  have key := h Unit Unit (lemma611MDP γ hγ0 hγ1) lemma611UnitDist (fun _ ↦ ())
    (fun s ↦ by simp [actionMaximum]) (9 / 10) 1 (fun _ ↦ 1) (by norm_num) (by norm_num) le_rfl
    (fun _ ↦ zero_le_one)
  have hdisc : (lemma611MDP γ hγ0 hγ1).discount = γ := rfl
  simp only [hdisc, Fintype.card_unique, Nat.cast_one, lemma611_unit_prob,
    DiscountedMDP.occupancyStateAt, mul_one, Finset.univ_unique, Finset.sum_singleton] at key
  rw [lemma611_H γ hγ8, lemma611_occ] at key
  have hW := lemma611_norm_le (fun _ : Unit ↦ (1 : ℝ)) (fun _ ↦ by norm_num)
  have hκ : γ * (1 + 1 / ((1 : ℕ) : ℝ)) ^ 3 = 8 * γ := by norm_num; ring
  rw [hκ, tsum_geometric_of_lt_one (by positivity) (by linarith)] at key
  have h8 : 1 - 8 * γ = (3 * C + 1)⁻¹ := by
    rw [hγ]; field_simp; ring
  rw [h8, inv_inv] at key
  have h1γ : 7 / 8 ≤ 1 - γ := by linarith
  have hinv : 1 / (1 - γ) ≤ 8 / 7 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hn0 : 0 ≤ ‖(fun _ : Unit ↦ (1 : ℝ))‖ := norm_nonneg _
  have hrhs : (1 : ℝ) / (1 - γ) + 9 / 10 * ‖(fun _ : Unit ↦ (1 : ℝ))‖ / (1 * 1 ^ 4 * (1 - γ)) ≤
      19 / 10 * (8 / 7) := by
    have : (1 : ℝ) / (1 - γ) + 9 / 10 * ‖(fun _ : Unit ↦ (1 : ℝ))‖ / (1 * 1 ^ 4 * (1 - γ)) =
        (1 + 9 / 10 * ‖(fun _ : Unit ↦ (1 : ℝ))‖) * (1 / (1 - γ)) := by
      ring
    rw [this]
    have h0 : 0 ≤ 1 / (1 - γ) := by positivity
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hrhs hC.le]

end StatisticalRL.OfflineRL
