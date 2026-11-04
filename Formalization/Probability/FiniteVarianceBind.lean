import Formalization.Probability.FiniteTotalVariance

/-! Exact total variance of a finite mixture. This is an algebraic identity;
it does not yet establish any adaptive episode conditional law. -/
namespace StatisticalRL.OnlineRL
variable {State Outcome : Type*} [Fintype State] [Fintype Outcome]

theorem finite_variance_bind
    (p : FiniteDistribution State) (q : State → FiniteDistribution Outcome)
    (f : Outcome → ℝ) :
    (p.bind q).variance f =
      p.variance (fun x => (q x).expectation f) + p.expectation (fun x => (q x).variance f) := by
  simp only [FiniteDistribution.variance, FiniteDistribution.expectation_bind,
    FiniteDistribution.expectation_sub]
  ring
end StatisticalRL.OnlineRL
