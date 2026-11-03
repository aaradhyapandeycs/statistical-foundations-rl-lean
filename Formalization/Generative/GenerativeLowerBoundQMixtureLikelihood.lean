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

/-- Empty rows have likelihood one regardless of p and q. -/
theorem qMixtureRowLikelihood_zero (p q : ℝ) (x : Fin 0 → Bool) :
    qMixtureRowLikelihood 0 p q x = 1 := by simp [qMixtureRowLikelihood]

/-- The one-draw mean of the likelihood ratio under Bernoulli(p). -/
theorem qMixtureLikelihood_one_mean (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * qMixtureBernoulliLikelihood p q true +
      (1 - p) * qMixtureBernoulliLikelihood p q false = 1 := by
  simp [qMixtureBernoulliLikelihood]
  field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hp1)]
  ring

/-- The one-draw squared likelihood has the exact chi-square factor. -/
theorem qMixtureLikelihood_one_second_moment (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * (qMixtureBernoulliLikelihood p q true) ^ 2 +
      (1 - p) * (qMixtureBernoulliLikelihood p q false) ^ 2 =
        1 + (q-p)^2 / (p * (1-p)) := by
  simpa [qMixtureBernoulliLikelihood] using
    qMixture_bernoulli_likelihood_second_moment p q hp hp1

end StatisticalRL.GenerativeLowerBound
