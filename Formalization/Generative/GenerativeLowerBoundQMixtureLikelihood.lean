import Formalization.Generative.GenerativeLowerBoundQMixtureObservation
import Formalization.Generative.GenerativeLowerBoundQMixtureMoment
import Mathlib.MeasureTheory.Integral.Pi

/-! Likelihood ratios for one changed active Bernoulli row. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The actual coordinate likelihood ratio of Bernoulli(q) over Bernoulli(p).
For interior p both denominators are nonzero. -/
noncomputable def qMixtureBernoulliLikelihood (p q : ℝ) (b : Bool) : ℝ :=
  if b then q / p else (1 - q) / (1 - p)

/-- The likelihood factor for N observations of one row; N=0 gives 1. -/
noncomputable def qMixtureRowLikelihood (N : ℕ) (p q : ℝ) (x : Fin N → Bool) : ℝ :=
  ∏ t, qMixtureBernoulliLikelihood p q (x t)

/-- A single changed row's likelihood on the complete active-coordinate
array, shared by every hypothesis and every estimator. -/
noncomputable def qMixtureRowLikelihoodOnArray {m A N : ℕ} (p q : ℝ)
    (θ : Fin m × Fin A) (x : QMixtureActiveCoordinates m A N → Bool) : ℝ :=
  qMixtureRowLikelihood N p q (fun t ↦ x (θ,t))

/-- The finite uniform mixture likelihood, with exactly m*A alternatives. -/
noncomputable def qMixtureLikelihood {m A N : ℕ} (p q : ℝ)
    (x : QMixtureActiveCoordinates m A N → Bool) : ℝ :=
  (∑ θ : Fin m × Fin A, qMixtureRowLikelihoodOnArray p q θ x) / (m * A)

end StatisticalRL.GenerativeLowerBound
