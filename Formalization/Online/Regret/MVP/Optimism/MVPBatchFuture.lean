import Formalization.Online.Regret.MVP.Optimism.MVPBatchLaw
import Formalization.Generative.FiniteHorizonGenerativeSampling

/-! Actual expanded product rows and strictly later-stage samples. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpBatchFutureStateMeasurable : MeasurableSpace State := ⊤

/-- The l-th noninitial batch is a deterministic slice of the expanded row. -/
theorem mvp_futureData_indep_batch {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (hn : 2*n ≤ K) (h : Fin H) (s : State) (a : Action) :
    IndepFun (futureData (State := State) (Action := Action) h K)
      (fun data : Samples State Action H K =>
        mvpBatchSlice K n hn (fun i => data ((h,s,a),i))) (samplingLaw E K) := by
  have hm : Measurable (mvpBatchSlice (State := State) K n hn) := measurable_of_countable _
  exact (futureData_indep_row E K h s a).comp measurable_id hm

theorem mvp_batch_expanded_law {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (hn : 2*n ≤ K) (h : Fin H) (s : State) (a : Action) :
    (samplingLaw E K).map (fun data : Samples State Action H K =>
      mvpBatchSlice K n hn (fun i => data ((h,s,a),i))) =
      ((E h).transition s a).sampleMeasure n := by
  let row : Samples State Action H K → (Fin K → State) := fun data i => data ((h,s,a),i)
  have hr : Measurable row := measurable_of_countable _
  have hs : Measurable (mvpBatchSlice (State := State) K n hn) := measurable_of_countable _
  change (samplingLaw E K).map (mvpBatchSlice K n hn ∘ row) = _
  rw [← Measure.map_map hs hr, samplingLaw_row E K h s a]
  exact mvpBatchSlice_law ((E h).transition s a) K n hn
end StatisticalRL.FiniteHorizonGenerative
