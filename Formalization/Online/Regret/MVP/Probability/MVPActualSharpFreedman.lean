import Formalization.Online.Regret.MVP.Probability.MVPActualSharpCap

/-! Aggregate Freedman on actual masked batch increments, with batch-size cap. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualFixedMask_sharpFreedman {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (hn : 2*n ≤ K) (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ h s a code x, 0 ≤ V h s a code x ∧ V h s a code x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let M := H * Fintype.card (State × Action × Fin K)
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let X := mvpPaddedRevealIncrement order d (mvpActualPredictableTest H K n mask V)
    let σ₂ := (n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2
    1 - δ ≤ (samplingLaw E K).real {data |
      |StatisticalRL.incrementSum X M data| ≤
        Real.sqrt (8 * max
          (StatisticalRL.predictableSecondMomentSum (samplingLaw E K)
            (mvpRevealFiltration (Outcome := State) order) X M data)
          (σ₂ / (2 : ℝ)^peels) * Real.log (2 * peels / δ)) +
          (4/3) * H * Real.log (2 * peels / δ)} := by
  let order := mvpExpandedOrder (State := State) (Action := Action) H K
  let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
  let F := mvpActualPredictableTest H K n mask V
  exact StatisticalRL.freedman_source_bound (onlineStackProductLaw d)
    (mvpRevealFiltration (Outcome := State) order) (mvpPaddedRevealIncrement order d F)
    (H : ℝ) ((n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2)
    (by positivity) (by positivity)
    (mvp_paddedRevealIncrement_adapted order d F)
    (fun k => Filter.Eventually.of_forall
      (mvp_paddedRevealIncrement_bound order d F (H : ℝ) (by positivity)
        (mvp_actualPredictableTest_bounds H K n mask V hV) k))
    (mvp_paddedRevealIncrement_centered order (mvpExpandedOrder_injective H K) d F)
    (H * Fintype.card (State × Action × Fin K)) peels hp
    (mvp_actualPredictableVariance_le_batchCap E K n hn mask V hV) δ hδ hδ1
end StatisticalRL.FiniteHorizonGenerative
