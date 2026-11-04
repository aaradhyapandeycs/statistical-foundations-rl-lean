import Formalization.Online.SourceOptimism.FreshCoordinateSelection

/-! Conditional mean for an arbitrary revealed-code-dependent finite test. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance : MeasurableSpace Outcome := ⊤

/-- The true conditional mean under the actual finite product law: the test
is fixed by the revealed coordinates, while the sampled coordinate is fresh. -/
theorem mvp_revealedTest_condExp
    (d : Index → FiniteDistribution Outcome) (I : Finset Index)
    (i : Index) (hi : i ∉ I)
    (F : ((j : I) → Outcome) → Outcome → ℝ) :
    (onlineStackProductLaw d)[(fun data => F (onlineRevealedCode I data) (data i)) |
      onlineRevealedSigma I] =ᵐ[onlineStackProductLaw d]
      (fun data => (d i).expectation (F (onlineRevealedCode I data))) := by
  classical
  let coeff := fun (x : Outcome) (data : Index → Outcome) => F (onlineRevealedCode I data) x
  let indicator := fun (x : Outcome) (data : Index → Outcome) => if data i = x then (1 : ℝ) else 0
  have hcoeff (x : Outcome) : StronglyMeasurable[onlineRevealedSigma I] (coeff x) := by
    exact ((measurable_of_countable (fun code => F code x)).comp (comap_measurable _)).stronglyMeasurable
  have hsum := condExp_finset_sum (μ := onlineStackProductLaw d) (s := Finset.univ)
    (f := fun x => coeff x * indicator x) (fun _ _ => Integrable.of_finite)
    (onlineRevealedSigma I)
  have hterms := ae_all_iff.mpr (fun x : Outcome =>
    (condExp_mul_of_stronglyMeasurable_left (hcoeff x)
      (Integrable.of_finite) (Integrable.of_finite)).trans
      ((Filter.EventuallyEq.refl _ _).mul
        (onlineUnrevealedIndicator_condExp d I i hi x)))
  have hleft : (∑ x : Outcome, coeff x * indicator x) =
      (fun data => F (onlineRevealedCode I data) (data i)) := by
    funext data
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_eq_single (data i)]
    · simp [coeff, indicator]
    · intro x _ hx
      simp [indicator, Ne.symm hx]
    · simp
  rw [hleft] at hsum
  filter_upwards [hsum, hterms] with data hs ht
  rw [hs]
  simp only [Finset.sum_apply]
  calc
    _ = ∑ x : Outcome, coeff x data * (d i).prob x := by
      apply Finset.sum_congr rfl
      intro x _
      exact ht x
    _ = _ := by simp only [FiniteDistribution.expectation, coeff]; apply Finset.sum_congr rfl; intro x _; ring
end StatisticalRL.OnlineRL
