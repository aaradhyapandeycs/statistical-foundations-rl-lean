import Formalization.Online.Regret.Gap.OnlineJ1GapProcess

/-! Actual-law variance and gap proof component: OnlineJ1Variance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
variable {State : Type*} [Fintype State]

theorem onlineJ1_clipped_variance_le_gap_square
    (p : FiniteDistribution State) (H : ℝ) (hH : 0 ≤ H)
    (U P : State → ℝ) :
    p.variance (fun s => onlineJ1Clip H (U s - P s)) ≤
      p.expectation (fun s => (U s - P s)^2) := by
  apply (p.variance_le_expectation_sq _).trans
  apply p.expectation_mono
  intro s
  exact onlineJ1Clip_sq_le H (U s - P s) hH
end StatisticalRL.OnlineRL
