import Formalization.Online.Regret.MVP.Probability.MVPActualFreedman

/-! Regroup exact predictable variation by the actual expanded coordinates. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualPredictableVariance_groupCoordinates {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K n : ℕ)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ) :
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let F := mvpActualPredictableTest H K n mask V
    StatisticalRL.predictableSecondMomentSum (samplingLaw E K)
      (mvpRevealFiltration (Outcome := State) order) (mvpPaddedRevealIncrement order d F)
        (H * Fintype.card (State × Action × Fin K)) =ᵐ[samplingLaw E K]
      fun data => ∑ coord : SampleIndex State Action H K,
        if mask coord.1.1 coord.1.2.1 coord.1.2.2 &&
            decide (n ≤ coord.2.val ∧ coord.2.val < 2*n) then
          ((E coord.1.1).transition coord.1.2.1 coord.1.2.2).variance
            (V coord.1.1 coord.1.2.1 coord.1.2.2 (futureData coord.1.1 K data))
        else 0 := by
  classical
  let order := mvpExpandedOrder (State := State) (Action := Action) H K
  let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
  let F := mvpActualPredictableTest H K n mask V
  have hv := mvp_reveal_predictableSecondMomentSum order (mvpExpandedOrder_injective H K) d F
  filter_upwards [hv] with data hdata
  change StatisticalRL.predictableSecondMomentSum (onlineStackProductLaw d)
    (mvpRevealFiltration (Outcome := State) order) (mvpPaddedRevealIncrement order d F)
    (H * Fintype.card (State × Action × Fin K)) data = _
  rw [hdata]
  let equiv := Equiv.ofBijective order ⟨mvpExpandedOrder_injective H K, mvpExpandedOrder_surjective H K⟩
  apply Fintype.sum_equiv equiv
  intro j
  dsimp [equiv, order, d, F, mvpActualPredictableTest]
  rw [mvpFutureCodeFromPrefix_actual]
  split <;> simp [FiniteDistribution.variance_const]
end StatisticalRL.FiniteHorizonGenerative
