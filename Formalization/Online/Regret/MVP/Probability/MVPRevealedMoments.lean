import Formalization.Probability.Variance
import Formalization.Online.Regret.MVP.Probability.MVPRevealedTest

/-! Actual conditional first and centered second moments for a revealed test. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance : MeasurableSpace Outcome := ⊤

theorem mvp_revealedCenteredTest_mean
    (d : Index → FiniteDistribution Outcome) (I : Finset Index)
    (i : Index) (hi : i ∉ I) (F : ((j : I) → Outcome) → Outcome → ℝ) :
    (onlineStackProductLaw d)[(fun data =>
      F (onlineRevealedCode I data) (data i) -
        (d i).expectation (F (onlineRevealedCode I data))) |
      onlineRevealedSigma I] =ᵐ[onlineStackProductLaw d] 0 := by
  have h := mvp_revealedTest_condExp d I i hi
    (fun code x => F code x - (d i).expectation (F code))
  filter_upwards [h] with data hd
  rw [hd]
  simp [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]

theorem mvp_revealedCenteredTest_secondMoment
    (d : Index → FiniteDistribution Outcome) (I : Finset Index)
    (i : Index) (hi : i ∉ I) (F : ((j : I) → Outcome) → Outcome → ℝ) :
    (onlineStackProductLaw d)[(fun data =>
      (F (onlineRevealedCode I data) (data i) -
        (d i).expectation (F (onlineRevealedCode I data)))^2) |
      onlineRevealedSigma I] =ᵐ[onlineStackProductLaw d]
      (fun data => (d i).variance (F (onlineRevealedCode I data))) := by
  have h := mvp_revealedTest_condExp d I i hi
    (fun code x => (F code x - (d i).expectation (F code))^2)
  filter_upwards [h] with data hd
  rw [hd, FiniteDistribution.variance_eq_expectation_centered_sq]
end StatisticalRL.OnlineRL
