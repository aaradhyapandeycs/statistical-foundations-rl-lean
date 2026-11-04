import Formalization.Online.Regret.W2.OnlineW2CoordinateStack

/-! Fixed-coordinate expectation and variance identities for the W₂
coordinate Bernstein event. No adaptive or probabilistic claim is made here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State : Type*} [Fintype State]
noncomputable local instance w2IndicatorDecidable : DecidableEq State := Classical.decEq State

/-- The indicator's mean is exactly the coordinate probability. -/
theorem onlineW2Indicator_expectation (p : FiniteDistribution State) (x : State) :
    p.expectation (onlineW2Indicator x) = p.prob x := by
  classical
  simp [FiniteDistribution.expectation, onlineW2Indicator]

/-- Bernoulli variance is at most the corresponding true row probability,
including zero-probability coordinates. -/
theorem onlineW2Indicator_variance_le (p : FiniteDistribution State) (x : State) :
    p.variance (onlineW2Indicator x) ≤ p.prob x := by
  have h := p.variance_le_expectation_sq (onlineW2Indicator x)
  have he : (fun s => (onlineW2Indicator x s)^2) = onlineW2Indicator x := by
    funext s
    simp [onlineW2Indicator]
  rw [he, onlineW2Indicator_expectation] at h
  exact h
end StatisticalRL.OnlineRL
