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

end StatisticalRL.FiniteHorizonGenerative
