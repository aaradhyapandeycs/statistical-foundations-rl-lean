import Formalization.Probability.Variance

/-! Finite conditional total-variance identity, the algebraic core of the
fixed-policy episodic variance telescope. The outer and inner rows are identified with the actual
trajectory law by the consuming variance decomposition. -/
namespace StatisticalRL.OnlineRL
variable {State Outcome : Type*} [Fintype State] [Fintype Outcome]

theorem finite_conditional_total_variance
    (p : FiniteDistribution State) (q : State → FiniteDistribution Outcome)
    (f : State → Outcome → ℝ) :
    p.expectation (fun x => (q x).expectation (fun y => (f x y)^2)) -
      (p.expectation (fun x => (q x).expectation (f x)))^2 =
      p.variance (fun x => (q x).expectation (f x)) +
        p.expectation (fun x => (q x).variance (f x)) := by
  simp only [FiniteDistribution.variance, FiniteDistribution.expectation_sub]
  ring
end StatisticalRL.OnlineRL
