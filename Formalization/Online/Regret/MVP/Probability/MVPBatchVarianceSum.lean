import Formalization.Online.Regret.MVP.Probability.MVPActualVarianceGrouping
import Formalization.Online.Regret.MVP.Probability.MVPBatchCard

/-! Exact n-fold grouping of actual selected-row variances. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_batchVariance_coordinate_sum {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K n : ℕ) (hn : 2*n ≤ K)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (data : Samples State Action H K) :
    (∑ coord : SampleIndex State Action H K,
        if mask coord.1.1 coord.1.2.1 coord.1.2.2 &&
            decide (n ≤ coord.2.val ∧ coord.2.val < 2*n) then
          ((E coord.1.1).transition coord.1.2.1 coord.1.2.2).variance
            (V coord.1.1 coord.1.2.1 coord.1.2.2 (futureData coord.1.1 K data))
        else 0) =
      (n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then ((E h).transition s a).variance (V h s a (futureData h K data)) else 0 := by
  classical
  simp only [SampleIndex, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  cases hm : mask h s a with
  | false => simp [hm]
  | true =>
    simpa using mvp_batch_indicator_sum K n hn
      (((E h).transition s a).variance (V h s a (futureData h K data)))
end StatisticalRL.FiniteHorizonGenerative
