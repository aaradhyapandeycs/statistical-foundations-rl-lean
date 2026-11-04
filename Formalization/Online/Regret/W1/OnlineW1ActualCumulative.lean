import Formalization.Online.Regret.W1.OnlineW1RadiusAggregation

/-! OnlineW1ActualCumulative: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w1CumulativeStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance OnlineW1ActualCumulativeLocalInstance1 : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1ActualCumulativeLocalInstance2 : DecidableEq Action := Classical.decEq Action

/-- True optimal-continuation transition variance along the actual path. -/
noncomputable def onlineActualW1T6Optimal
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    onlineActualW1Variance H K hH E initial fallback path δ c₁ c₂ h k

/-- The observed two-sided event controls actual W₁ by a true-variance term,
a harmonic visit-count term, and the explicit ≤3 visits per row low-count
charge. This is not yet the source's W₁/W₂ or regret-rate theorem. -/
theorem onlineActualW1_le_trueVarianceBudget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hcert : onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path)) :
    let L := Real.log (1 / (2 * δ))
    let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
    let R := A * (1 + Real.log (K + 1 : ℝ))
    (∑ k : Fin K, onlineActualEpisodeW1 H K hH E initial fallback path k δ c₁ c₂) ≤
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
  have hpoint : (∑ k : Fin K, onlineActualEpisodeW1 H K hH E initial fallback path k δ c₁ c₂) ≤
      ∑ i : Fin H × Fin K, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ i.1 i.2 := by
    calc
      _ ≤ ∑ k : Fin K, onlineActualEpisodeW1RadiusSum H K hH E initial fallback path k δ c₁ c₂ :=
        Finset.sum_le_sum (fun k _ => onlineActualEpisodeW1_le_radiusSum H K hH E initial fallback path k δ c₁ c₂ hcert)
      _ = _ := by
        simp only [onlineActualEpisodeW1RadiusSum_eq, Fintype.sum_prod_type]
        exact Finset.sum_comm
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
  rw [heq] at hpoint
  rw [hvariance] at hagg
  change _ ≤ (H : ℝ) * (3 * A) + Real.sqrt (2 * L * onlineActualW1T6Optimal H K hH E initial fallback path δ c₁ c₂) * Real.sqrt R + (2 * H * L / 3) * R
  linarith
end StatisticalRL.OnlineRL
