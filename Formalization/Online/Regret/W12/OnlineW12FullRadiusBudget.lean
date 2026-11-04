import Formalization.Online.Regret.W12.OnlineW12SuffixEnvelope
import Formalization.Online.Regret.W1.OnlineW1ActualCumulative
import Formalization.Online.Regret.W2.OnlineW2ActualCumulative

/-! Same-experiment suffix proof component: OnlineW12FullRadiusBudget.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w12BudgetState : DecidableEq State := Classical.decEq State
noncomputable local instance w12BudgetAction : DecidableEq Action := Classical.decEq Action
theorem onlineActualW1_fullRadius_le_trueVarianceBudget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
 :
    let L := Real.log (1 / (2 * δ))
    let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
    let R := A * (1 + Real.log (K + 1 : ℝ))
    (∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      (H : ℝ) * (3 * A) +
      Real.sqrt (2 * L * onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂) * Real.sqrt R +
      (2 * H * L / 3) * R := by
  classical
  let L := Real.log (1 / (2 * δ))
  let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
  let R := A * (1 + Real.log (K + 1 : ℝ))
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let count := fun i : Fin H × Fin K => onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ i.1 i.2
  let variance := fun i : Fin H × Fin K => onlineActualW1Variance H K hH E initial fallback path δ c₁ c₂ i.1 i.2
  have hL : 0 ≤ L := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
    linarith
  have hv : ∀ i, 0 ≤ variance i := by
    intro i
    exact FiniteDistribution.variance_nonneg _ _
  have hlow : (∑ i : Fin H × Fin K, if count i < 3 then (1 : ℝ) else 0) ≤ 3 * A := by
    have h := onlineSequential_lowCount_visits_le H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, A, Fintype.sum_prod_type, mul_assoc] using h
  have hinv : (∑ i : Fin H × Fin K, (count i : ℝ)⁻¹) ≤ R := by
    have h := onlineSequential_reciprocalCount_budget H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, R, A, Fintype.sum_prod_type, mul_assoc] using h
  have hvariance : (∑ i : Fin H × Fin K, variance i) =
      onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂ := by
    simp [variance, onlineActualW1T6Optimal, Fintype.sum_prod_type]
  have hagg := onlineW1_trueRadius_sum_le (Finset.univ : Finset (Fin H × Fin K))
    count variance H δ (by exact_mod_cast Nat.zero_le H) hδ hδsmall hv
  have heq : (∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) =
      ∑ i : Fin H × Fin K, if 3 ≤ count i then
        Real.sqrt (2 * L * variance i / count i) + 2 * H * L / (3 * count i) else H := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinv)
    (Real.sqrt_nonneg (2 * L * onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂))
  have hlin := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * H * L / 3 by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ H by exact_mod_cast Nat.zero_le H)
  rw [heq]
  rw [hvariance] at hagg
  change _ ≤ (H : ℝ) * (3 * A) + Real.sqrt (2 * L * onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂) * Real.sqrt R + (2 * H * L / 3) * R
  linarith
theorem onlineActualW2_fullRadius_le_policyDifferenceBudget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
 :
    let S := (Fintype.card State : ℝ)
    let A := S * (Fintype.card Action : ℝ) * H
    let L := Real.log (1 / δ)
    let R := A * (1 + Real.log (K + 1 : ℝ))
    (∑ i : Fin H × Fin K, onlineActualW2RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) ≤
      H * (3 * A) +
      Real.sqrt (2 * (S * L) * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂) * Real.sqrt R +
      S * H * L * R := by
  classical
  let S := (Fintype.card State : ℝ)
  let A := S * (Fintype.card Action : ℝ) * H
  let L := Real.log (1 / δ)
  let R := A * (1 + Real.log (K + 1 : ℝ))
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let count := fun i : Fin H × Fin K => onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ i.1 i.2
  let variance := fun i : Fin H × Fin K =>
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path i.1 i.2.val
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ i.1 i.2
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ i.1 i.2
    ((E i.1).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  have hv : ∀ i, 0 ≤ variance i := by
    intro i
    exact FiniteDistribution.expectation_nonneg _ (fun s => sq_nonneg _)
  have hlow : (∑ i : Fin H × Fin K, if count i < 3 then (1 : ℝ) else 0) ≤ 3 * A := by
    have h := onlineSequential_lowCount_visits_le H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, L, A, S, Fintype.sum_prod_type, mul_assoc] using h
  have hinv : (∑ i : Fin H × Fin K, (count i : ℝ)⁻¹) ≤ R := by
    have h := onlineSequential_reciprocalCount_budget H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, L, R, A, S, Fintype.sum_prod_type, mul_assoc] using h
  have hvariance : (∑ i : Fin H × Fin K, variance i) =
      onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ := by
    simp [variance, planner, L, onlineActualT6Difference, Fintype.sum_prod_type]
  have hagg := onlineW2_radius_sum_le (Finset.univ : Finset (Fin H × Fin K)) count variance S H L
    (by positivity) (by exact_mod_cast Nat.zero_le H) hL hv
  have heq : (∑ i : Fin H × Fin K, onlineActualW2RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2) =
      ∑ i : Fin H × Fin K, if 3 ≤ count i then
        Real.sqrt (2 * S * L * variance i / count i) + S * H * L / count i else H := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [heq]
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinv)
    (Real.sqrt_nonneg (2 * (S * L) * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂))
  have hlin := mul_le_mul_of_nonneg_left hinv (show 0 ≤ S * H * L by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ H by exact_mod_cast Nat.zero_le H)
  rw [hvariance] at hagg
  change _ ≤ (H : ℝ) * (3 * A) + Real.sqrt (2 * (S * L) * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂) * Real.sqrt R + S * H * L * R
  linarith
end StatisticalRL.OnlineRL
