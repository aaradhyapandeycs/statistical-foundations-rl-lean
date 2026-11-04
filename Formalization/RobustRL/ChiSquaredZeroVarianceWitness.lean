import Formalization.ModelFree.QLearningRobustComparator
import Formalization.RobustRL.ChiSquaredPrimalDualWeakBridge

/-! χ² ZeroVarianceWitness for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/
namespace StatisticalRL.RobustRL.ChiSquaredZeroVarianceWitness

variable {State : Type*} [Fintype State]

theorem nominal_zero_variance_witness
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (σ b : ℝ)
    (hσ : 0 ≤ σ) (hv : p.variance V = 0) (hb : ∀ s, V s ≤ b) :
    p ∈ StatisticalRL.QLearning.qChiBall p σ ∧
    StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective p V σ b =
      p.expectation V := by
  have hc : (fun s ↦ min (V s) b) = V := by
    funext s
    exact min_eq_left (hb s)
  refine ⟨StatisticalRL.QLearning.qChiBall_self p σ hσ, ?_⟩
  simp [StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective, hc, hv]
end StatisticalRL.RobustRL.ChiSquaredZeroVarianceWitness
