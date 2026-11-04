import Formalization.Counterexamples.CenteredSquareVariance
import Formalization.Probability.EmpiricalBernstein

/-! The two-point signed counterexample under the measure-theoretic variance. -/
namespace StatisticalRL.SourceCounterexamples
open MeasureTheory ProbabilityTheory

noncomputable def squareVarianceMeasure : Measure (Fin 1 → Bool) :=
  squareVarianceLaw.sampleMeasure 1

def squareVarianceSample (ω : Fin 1 → Bool) : ℝ := signedValue (ω 0)

theorem squareVarianceSample_measurable : Measurable squareVarianceSample :=
  FiniteDistribution.sampleValue_measurable signedValue 1 0

theorem squareVarianceSample_abs (ω : Fin 1 → Bool) : |squareVarianceSample ω| = 1 :=
  signedValue_abs (ω 0)

theorem squareVarianceSample_mean :
    (∫ ω, squareVarianceSample ω ∂squareVarianceMeasure) = -(3 / 4 : ℝ) := by
  rw [show (∫ ω, squareVarianceSample ω ∂squareVarianceMeasure) =
    squareVarianceLaw.expectation signedValue from
      squareVarianceLaw.sampleMeasure_coordinate_integral 1 0 signedValue]
  exact squareVarianceLaw_mean

theorem centeredSquare_measure_coefficient_one_false :
    ¬ ProbabilityTheory.variance
        (fun ω => (squareVarianceSample ω - ∫ z, squareVarianceSample z ∂squareVarianceMeasure)^2)
          squareVarianceMeasure ≤
      (1 : ℝ)^2 * ProbabilityTheory.variance squareVarianceSample squareVarianceMeasure := by
  rw [squareVarianceSample_mean]
  have h1 := squareVarianceLaw.sampleValue_variance signedValue 1 0
  have h2 := squareVarianceLaw.sampleValue_variance
    (fun b => (signedValue b - squareVarianceLaw.expectation signedValue)^2) 1 0
  rw [squareVarianceLaw_mean] at h2
  change ProbabilityTheory.variance squareVarianceSample squareVarianceMeasure = _ at h1
  change ProbabilityTheory.variance (fun ω => (squareVarianceSample ω - -(3 / 4 : ℝ))^2)
    squareVarianceMeasure = _ at h2
  have h3 := squareVarianceLaw_centeredSquare_variance
  rw [squareVarianceLaw_mean] at h3
  rw [h1, h2, squareVarianceLaw_variance, h3]
  norm_num
end StatisticalRL.SourceCounterexamples
