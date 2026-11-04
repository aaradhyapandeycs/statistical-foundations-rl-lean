import Formalization.ModelFree.QLearningRobustDefinitions

/-! χ² Density for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.ChiSquaredDensity

variable {State : Type*} [Fintype State]

/-- A nonnegative unit-mean density defines an actual finite probability row. -/
noncomputable def densityRow (p : FiniteDistribution State) (w : State → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : p.expectation w = 1) :
    FiniteDistribution State where
  prob x := p.prob x * w x
  prob_nonneg x := mul_nonneg (p.prob_nonneg x) (hw x)
  sum_prob := hnorm

@[simp]
theorem densityRow_prob (p : FiniteDistribution State) (w : State → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : p.expectation w = 1) (x : State) :
    (densityRow p w hw hnorm).prob x = p.prob x * w x := rfl

/-- Reweighting cannot create mass outside the nominal support. -/
theorem densityRow_support (p : FiniteDistribution State) (w : State → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : p.expectation w = 1) (x : State)
    (hp : p.prob x = 0) : (densityRow p w hw hnorm).prob x = 0 := by
  simp [densityRow_prob, hp]

/-- Its Pearson cost is the nominal centered density second moment, including
nominal zero atoms without cancellation at zero. -/
theorem densityRow_chiSquared (p : FiniteDistribution State) (w : State → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : p.expectation w = 1) :
    StatisticalRL.QLearning.qChiSquared p (densityRow p w hw hnorm) =
      p.expectation (fun x ↦ (w x - 1) ^ 2) := by
  classical
  unfold StatisticalRL.QLearning.qChiSquared FiniteDistribution.expectation
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x),
        p.prob x * (w x - 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hp : p.prob x ≠ 0 := ne_of_gt (Finset.mem_filter.mp hx).2
      rw [densityRow_prob]
      field_simp
    _ = ∑ x, p.prob x * (w x - 1) ^ 2 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hx hnot
      have hp : p.prob x = 0 := by
        have hn : ¬ 0 < p.prob x := by simpa using hnot
        exact le_antisymm (le_of_not_gt hn) (p.prob_nonneg x)
      simp [hp]

/-- Expected values under the actual row are nominal density-weighted values. -/
theorem densityRow_expectation (p : FiniteDistribution State) (w V : State → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : p.expectation w = 1) :
    (densityRow p w hw hnorm).expectation V =
      p.expectation (fun x ↦ w x * V x) := by
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x hx
  rw [densityRow_prob]
  ring

/-- The cost identity and support proof place the constructed row in the actual
library uncertainty ball, once its scalar density cost is established. -/
theorem densityRow_mem_ball (p : FiniteDistribution State) (w : State → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : p.expectation w = 1) (σ : ℝ)
    (hcost : p.expectation (fun x ↦ (w x - 1) ^ 2) ≤ σ) :
    densityRow p w hw hnorm ∈ StatisticalRL.QLearning.qChiBall p σ := by
  constructor
  · exact densityRow_support p w hw hnorm
  · rw [densityRow_chiSquared]
    exact hcost

end StatisticalRL.RobustRL.ChiSquaredDensity
