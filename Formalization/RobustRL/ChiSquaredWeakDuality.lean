import Formalization.ModelFree.QLearningChiUpper

/-!
# χ² weak duality for finite probability rows

The manuscript's clipped nominal expectation minus the square root of radius
times clipped nominal variance is a lower bound for each support-aware
χ²-feasible row. The pointwise bound holds for every clipping threshold; it
does not establish the manuscript's infimum/maximum equality.
-/

namespace StatisticalRL.RobustRL.ChiSquaredWeakDuality

variable {State : Type*} [Fintype State]

/-- The source clipped scalar objective is below the expected value of each
support-aware χ²-feasible row. -/
theorem clipped_scalar_le_feasible_expectation
    (p q : FiniteDistribution State) (V : State → ℝ) (σ α : ℝ)
    (hq : q ∈ StatisticalRL.QLearning.qChiBall p σ) :
    p.expectation (fun s ↦ min (V s) α) -
        Real.sqrt (σ * p.variance (fun s ↦ min (V s) α)) ≤
      q.expectation V := by
  have hmono : q.expectation (fun s ↦ min (V s) α) ≤ q.expectation V := by
    apply q.expectation_mono
    intro s
    exact min_le_left _ _
  have hdev := StatisticalRL.QLearning.qChiBall_abs_expectation_sub_le
    p q σ (fun s ↦ min (V s) α) hq
  have hlower := neg_abs_le
    (q.expectation (fun s ↦ min (V s) α) -
      p.expectation (fun s ↦ min (V s) α))
  linarith

end StatisticalRL.RobustRL.ChiSquaredWeakDuality
