import Formalization.Online.Regret.W3.OnlineW3CombinedAggregation
import Formalization.Online.Regret.W1.OnlineW1PolicyVarianceBridge

/-! Coarse same-path W₃ bound from the fixed-square event, shared coordinate
event, and actual optimism. The source-iota absorption is separate. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3CoarseStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3CoarseActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineActualW3_le_coarseBudget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hfixed : onlineObservedW3SquareCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hcoord : onlineObservedW2CoordinateCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)) :
    let S := (Fintype.card State : ℝ)
    let A := S * (Fintype.card Action : ℝ) * H
    let L₀ := Real.log (1 / (2 * δ))
    let L := Real.log (1 / δ)
    let R := A * (1 + Real.log (K + 1 : ℝ))
    let p := onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂
    let d := onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂
    (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) ≤
      6 * H^2 * A + Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt R +
      Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt R +
      (2 * H^2 * L₀ / 3 + S * H^2 * L) * R := by
  classical
  let S := (Fintype.card State : ℝ)
  let A := S * (Fintype.card Action : ℝ) * H
  let L₀ := Real.log (1 / (2 * δ))
  let L := Real.log (1 / δ)
  let R := A * (1 + Real.log (K + 1 : ℝ))
  let p := onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂
  let d := onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let count := fun i : Fin H × Fin K => onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ i.1 i.2
  let fixed := fun i : Fin H × Fin K =>
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path i.1 i.2.val
    ((E i.1).transition sa.1 sa.2).variance (onlineW3SquaredTrueFamily H E (i.1, sa))
  let adaptive := fun i : Fin H × Fin K =>
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path i.1 i.2.val
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ i.1 i.2
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ i.1 i.2
    4 * (H : ℝ)^2 * ((E i.1).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)
  have hL₀ : 0 ≤ L₀ := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
    linarith
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  have hf : ∀ i, 0 ≤ fixed i := fun i => FiniteDistribution.variance_nonneg _ _
  have ha : ∀ i, 0 ≤ adaptive i := by
    intro i
    dsimp [adaptive]
    apply mul_nonneg (by positivity)
    exact FiniteDistribution.expectation_nonneg _ (fun s => sq_nonneg _)
  have hlow : (∑ i : Fin H × Fin K, if count i < 3 then (1 : ℝ) else 0) ≤ 3 * A := by
    have hh := onlineSequential_lowCount_visits_le H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, L, A, S, Fintype.sum_prod_type, mul_assoc] using hh
  have hinv : (∑ i : Fin H × Fin K, (count i : ℝ)⁻¹) ≤ R := by
    have hh := onlineSequential_reciprocalCount_budget H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, L, R, A, S, Fintype.sum_prod_type, mul_assoc] using hh
  have hfixedsum : (∑ i : Fin H × Fin K, fixed i) ≤ 4 * H^2 * (2 * p + 2 * d) := by
    have hv : (∑ i : Fin H × Fin K, fixed i) ≤
        4 * (H : ℝ)^2 * onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂ := by
      unfold onlineActualW1T6Optimal
      simp only [Finset.mul_sum, Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact onlineW3_square_variance_le _ _ H (by positivity)
        (onlineTrueSuffixRowFamily_range H E _)
    have ht := onlineActualT6Optimal_le_policy_difference H K hH E initial fallback path δ c₁ c₂ hoptimism
    have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * (H : ℝ)^2 by positivity)
    exact hv.trans hm
  have hadaptive : (∑ i : Fin H × Fin K, adaptive i) = 4 * H^2 * d := by
    simp [adaptive, planner, L, d, onlineActualT6Difference, Fintype.sum_prod_type, Finset.mul_sum]
  have hagg := onlineW3_combined_radius_sum_le (Finset.univ : Finset (Fin H × Fin K)) count fixed adaptive S H δ
    (by positivity) (by positivity) hδ hδsmall hf ha
  have hpoint : (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) ≤
      ∑ i : Fin H × Fin K, ((if 3 ≤ count i then
        Real.sqrt (2 * L₀ * fixed i / count i) + 2 * (H : ℝ)^2 * L₀ / (3 * count i) else (H : ℝ)^2) +
        (if 3 ≤ count i then Real.sqrt (2 * S * L * adaptive i / count i) + S * (H : ℝ)^2 * L / count i else (H : ℝ)^2)) := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro h hh
    apply Finset.sum_le_sum
    intro k hk
    rw [onlineActualW3Point_eq_fixed_add_adaptive]
    have hp := onlineActualW3FixedPoint_le_radius H K hH E initial fallback path δ c₁ c₂ hfixed h k
    have hq := onlineActualW3AdaptivePoint_le_radius H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ hcoord hoptimism h k
    simpa only [onlineTrueW1Radius, fixed, adaptive, count, planner, L₀, L, S, onlineW3SquaredTrueFamily] using add_le_add hp hq
  have hrootf := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hfixedsum (show 0 ≤ 2 * L₀ by positivity)))
    (Real.sqrt_nonneg (∑ i : Fin H × Fin K, (count i : ℝ)⁻¹))
  have hsumf : 0 ≤ ∑ i : Fin H × Fin K, fixed i := Finset.sum_nonneg (fun i _ => hf i)
  have hsuma : 0 ≤ ∑ i : Fin H × Fin K, adaptive i := Finset.sum_nonneg (fun i _ => ha i)
  have hr₁ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinv)
    (Real.sqrt_nonneg (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))))
  have hr₂ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinv)
    (Real.sqrt_nonneg (2 * (S * L) * (4 * H^2 * d)))
  have hsmall := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * (H : ℝ)^2 by positivity)
  have hlin := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * (H : ℝ)^2 * L₀ / 3 + S * H^2 * L by positivity)
  rw [hadaptive] at hagg
  change _ ≤ 6 * (H : ℝ)^2 * A + Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt R +
    Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt R + (2 * H^2 * L₀ / 3 + S * H^2 * L) * R
  linarith
end StatisticalRL.OnlineRL
