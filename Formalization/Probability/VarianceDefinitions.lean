import Formalization.MDP.CoreDefinitions

/-! Definition-only split of `FiniteDistribution.variance` from
`Formalization/Probability/Variance.lean` (eq:defn-Var-Psa-V). The three
lines below are byte-identical to the original declaration span. -/

namespace StatisticalRL

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

/-- Variance under the real finite probability simplex. -/
def variance (d : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  d.expectation (fun x ↦ f x ^ 2) - (d.expectation f) ^ 2

end FiniteDistribution

end StatisticalRL
