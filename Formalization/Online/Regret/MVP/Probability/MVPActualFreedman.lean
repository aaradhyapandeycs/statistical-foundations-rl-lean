import Formalization.Online.Regret.MVP.Probability.MVPActualTests

/-! Fixed chosen later-stage tests and masks on the actual expanded product law. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualPredictableTest_bounds (H K n : ℕ)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ h s a code x, 0 ≤ V h s a code x ∧ V h s a code x ≤ H)
    (j : Fin (H * Fintype.card (State × Action × Fin K)))
    (code : (i : mvpRevealedPrefix
      (mvpExpandedOrder (State := State) (Action := Action) H K) j.val) → State) (x : State) :
    0 ≤ mvpActualPredictableTest H K n mask V j code x ∧
      mvpActualPredictableTest H K n mask V j code x ≤ H := by
  classical
  unfold mvpActualPredictableTest
  split <;> simp_all

/-- Aggregate peeled Freedman for fixed masks and chosen later-stage tests
under the actual expanded product law. The source-specific grouping and
finite profile/choice union are separate obligations. -/
theorem mvp_actualFixedMask_freedman {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ h s a code x, 0 ≤ V h s a code x ∧ V h s a code x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let M := H * Fintype.card (State × Action × Fin K)
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let F := mvpActualPredictableTest H K n mask V
    let X := mvpPaddedRevealIncrement order d F
    1 - δ ≤ (samplingLaw E K).real {data |
      |StatisticalRL.incrementSum X M data| ≤
        Real.sqrt (8 * max
          (StatisticalRL.predictableSecondMomentSum (samplingLaw E K)
            (mvpRevealFiltration (Outcome := State) order) X M data)
          ((M : ℝ) * (H : ℝ)^2 / (2 : ℝ)^peels) * Real.log (2 * peels / δ)) +
          (4/3) * H * Real.log (2 * peels / δ)} := by
  let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
  have h := mvp_finiteProduct_freedman (mvpExpandedOrder H K)
    (mvpExpandedOrder_injective H K) d (mvpActualPredictableTest H K n mask V)
    (H : ℝ) (by positivity) (mvp_actualPredictableTest_bounds H K n mask V hV)
    peels hp δ hδ hδ1
  exact h
end StatisticalRL.FiniteHorizonGenerative
