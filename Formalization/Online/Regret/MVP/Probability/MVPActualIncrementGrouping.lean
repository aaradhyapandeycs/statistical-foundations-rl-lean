import Formalization.Online.Regret.MVP.Probability.MVPActualSharpFreedman

/-! Exact regrouping of actual fixed-mask martingale increments. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualIncrementSum_groupCoordinates {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K n : ℕ)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (data : Samples State Action H K) :
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let F := mvpActualPredictableTest H K n mask V
    StatisticalRL.incrementSum (mvpPaddedRevealIncrement order d F)
      (H * Fintype.card (State × Action × Fin K)) data =
      ∑ coord : SampleIndex State Action H K,
        if mask coord.1.1 coord.1.2.1 coord.1.2.2 &&
            decide (n ≤ coord.2.val ∧ coord.2.val < 2*n) then
          V coord.1.1 coord.1.2.1 coord.1.2.2 (futureData coord.1.1 K data) (data coord) -
          ((E coord.1.1).transition coord.1.2.1 coord.1.2.2).expectation
            (V coord.1.1 coord.1.2.1 coord.1.2.2 (futureData coord.1.1 K data))
        else 0 := by
  classical
  let order := mvpExpandedOrder (State := State) (Action := Action) H K
  let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
  let F := mvpActualPredictableTest H K n mask V
  change StatisticalRL.incrementSum (mvpPaddedRevealIncrement order d F) _ data = _
  unfold StatisticalRL.incrementSum
  rw [← Fin.sum_univ_eq_sum_range]
  let equiv := Equiv.ofBijective order ⟨mvpExpandedOrder_injective H K, mvpExpandedOrder_surjective H K⟩
  apply Fintype.sum_equiv equiv
  intro j
  simp only [mvpPaddedRevealIncrement, dif_pos j.isLt]
  dsimp [equiv, order, d, F, mvpActualPredictableTest]
  rw [mvpFutureCodeFromPrefix_actual]
  split <;> simp [FiniteDistribution.expectation_const]
end StatisticalRL.FiniteHorizonGenerative
