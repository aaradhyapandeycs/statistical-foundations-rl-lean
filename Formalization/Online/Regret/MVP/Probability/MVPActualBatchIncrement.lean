import Formalization.Online.Regret.MVP.Probability.MVPActualIncrementGrouping
import Formalization.Online.Regret.MVP.Probability.MVPBatchSliceSum

/-! Actual selected batch empirical errors equal the aggregate increments. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualIncrementSum_eq_batchErrors {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K n : ℕ) (hn : 2*n ≤ K) (hnpos : 0<n)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (data : Samples State Action H K) :
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let F := mvpActualPredictableTest H K n mask V
    StatisticalRL.incrementSum (mvpPaddedRevealIncrement order d F)
      (H * Fintype.card (State × Action × Fin K)) data =
      (n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then
          (FiniteDistribution.empiricalRow n hnpos ((fun j => data ((h,s,a),mvpBatchIndex K n hn j)))).expectation
              (V h s a (futureData h K data)) -
            ((E h).transition s a).expectation (V h s a (futureData h K data))
        else 0 := by
  classical
  dsimp only
  rw [mvp_actualIncrementSum_groupCoordinates E K n mask V data]
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
    simp only [Bool.true_and, decide_eq_true_eq, if_true]
    rw [mvp_batch_slice_sum K n hn]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [FiniteDistribution.empiricalRow_expectation]
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
    field_simp
    <;> ring
end StatisticalRL.FiniteHorizonGenerative
