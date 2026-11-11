import Formalization.Generative.GenerativeLowerBoundQMixtureOptimal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar likelihood second moment for one changed Bernoulli row. -/
namespace StatisticalRL.GenerativeLowerBound

/-- The genuine one-draw likelihood-ratio second moment, under the baseline
Bernoulli law, has the exact chi-square form. -/
theorem qMixture_bernoulli_likelihood_second_moment (p q : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    p * (q / p) ^ 2 + (1 - p) * ((1 - q) / (1 - p)) ^ 2 =
      1 + (q - p) ^ 2 / (p * (1 - p)) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp10 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  field_simp
  ring

end StatisticalRL.GenerativeLowerBound
