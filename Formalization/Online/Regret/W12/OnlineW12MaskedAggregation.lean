import Formalization.Online.Regret.W1.OnlineW1RadiusAggregation
import Formalization.Online.Regret.W2.OnlineW2RadiusAggregation

/-! Same-experiment suffix proof component: OnlineW12MaskedAggregation.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- A simultaneous absolute pointwise envelope controls any selected subset
by the full nonnegative radius sum. The subset may depend on the realized path. -/
theorem onlineW12_abs_masked_sum_le_full_radius {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (ht : t ⊆ s) (x radius : ι → ℝ)
    (hpoint : ∀ i ∈ s, |x i| ≤ radius i) :
    |∑ i ∈ t, x i| ≤ ∑ i ∈ s, radius i := by
  calc
    _ ≤ ∑ i ∈ t, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ t, radius i := Finset.sum_le_sum (fun i hi => hpoint i (ht hi))
    _ ≤ ∑ i ∈ s, radius i := Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun i hi hit => (abs_nonneg (x i)).trans (hpoint i hi))

end StatisticalRL.OnlineRL
