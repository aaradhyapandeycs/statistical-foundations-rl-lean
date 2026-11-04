import Formalization.Online.Regret.MVP.Probability.MVPActualFuturePrefix
import Formalization.Online.Regret.MVP.Probability.MVPFiniteProductFreedman

/-! Build predictable tests from genuinely later-stage expanded samples. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

noncomputable def mvpFutureCodeFromPrefix (H K : ℕ)
    (j : Fin (H * Fintype.card (State × Action × Fin K)))
    (code : (i : mvpRevealedPrefix
      (mvpExpandedOrder (State := State) (Action := Action) H K) j.val) → State) :
    FutureCode (State := State) (Action := Action)
      (mvpExpandedOrder (State := State) (Action := Action) H K j).1.1 K := by
  classical
  intro i
  apply code
  refine ⟨i.val, mvp_later_coord_mem_prefix H K j i.val ?_⟩
  exact (Finset.mem_filter.mp i.property).2

theorem mvpFutureCodeFromPrefix_actual (H K : ℕ)
    (j : Fin (H * Fintype.card (State × Action × Fin K)))
    (data : Samples State Action H K) :
    mvpFutureCodeFromPrefix H K j
      (onlineRevealedCode (mvpRevealedPrefix
        (mvpExpandedOrder (State := State) (Action := Action) H K) j.val) data) =
      futureData (mvpExpandedOrder (State := State) (Action := Action) H K j).1.1 K data := by
  rfl

/-- Deterministic stage/row masks, batch interval, and chosen future-code tests.
Zero outside the batch/mask preserves range and needs no conditional assumption. -/
noncomputable def mvpActualPredictableTest (H K n : ℕ)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (j : Fin (H * Fintype.card (State × Action × Fin K)))
    (code : (i : mvpRevealedPrefix
      (mvpExpandedOrder (State := State) (Action := Action) H K) j.val) → State) : State → ℝ := by
  classical
  let coord := mvpExpandedOrder (State := State) (Action := Action) H K j
  let h := coord.1.1
  let s := coord.1.2.1
  let a := coord.1.2.2
  let i := coord.2.val
  exact if mask h s a && decide (n ≤ i ∧ i < 2*n) then
    V h s a (mvpFutureCodeFromPrefix H K j code) else fun _ => 0
end StatisticalRL.FiniteHorizonGenerative
