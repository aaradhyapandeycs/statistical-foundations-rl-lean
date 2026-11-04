import Formalization.Online.Regret.MVP.Probability.MVPBatchVarianceSum

/-! Exact actual predictable variation grouped by selected row. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualPredictableVariance_eq_batchRows {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K n : ℕ) (hn : 2*n ≤ K)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ) :
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let F := mvpActualPredictableTest H K n mask V
    StatisticalRL.predictableSecondMomentSum (samplingLaw E K)
      (mvpRevealFiltration (Outcome := State) order) (mvpPaddedRevealIncrement order d F)
        (H * Fintype.card (State × Action × Fin K)) =ᵐ[samplingLaw E K]
      fun data => (n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then ((E h).transition s a).variance (V h s a (futureData h K data)) else 0 := by
  filter_upwards [mvp_actualPredictableVariance_groupCoordinates E K n mask V] with data hdata
  rw [hdata]
  exact mvp_batchVariance_coordinate_sum E K n hn mask V data
end StatisticalRL.FiniteHorizonGenerative
