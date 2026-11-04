import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.SourceOptimism.SuccessorStackPrefix

/-! A deterministic bridge from the finite-stack transcript to the MVP
planning-stage table. The source's auxiliary fixed-profile recursion has a
nonzero terminal initialization; this adapter follows the deployed recursion,
whose terminal continuation is zero. -/

namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance adapterStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance adapterStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance adapterActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Extracting rows and successors from a finite transcript and filtering
those arrays gives the transcript's chronological row outcomes. -/
theorem onlineMVPRowVisitList_history_eq
    {H : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (history : List (OnlineMDPRow State Action H × State))
    (n : ℕ) (hn : n ≤ history.length) (r : OnlineMDPRow State Action H) :
    onlineMVPRowVisitList
      (onlineMVPHistoryRowAt hH E fallback history)
      (onlineMVPHistoryNextAt fallback history) n r =
    onlineRowOutcomes (history.take n) r := by
  induction n with
  | zero => simp [onlineMVPRowVisitList, onlineRowOutcomes]
  | succ n ih =>
      have hlt : n < history.length := by omega
      rw [onlineMVPRowVisitList_succ,
        onlineMVPHistoryRowAt_eq_record hH E fallback history n hlt,
        onlineMVPHistoryNextAt_eq_record fallback history n hlt,
        ← List.take_concat_get' history n hlt,
        onlineRowOutcomes_append_one,
        ih (by omega)]
      simp

/-- The planner stages reconstructed from the actual stack transcript equal
the stages built directly from the sampler's row and successor arrays. This is
pathwise and makes no probability-law or independence claim. -/
theorem onlineMVPHistoryPlanningStages_actualStack_eq
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineMVPHistoryPlanningStages hH E fallback
        (onlineMVPActualStackHistory hH initial fallback planner data n) =
      List.ofFn (fun h : Fin H =>
        onlineMVPActualPlanningStage E
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data) n h) := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  unfold onlineMVPHistoryPlanningStages
  rw [List.ofFn_inj]
  funext h
  letI : Nonempty State := (E h).state_nonempty
  let history := onlineMVPActualStackHistory hH initial fallback planner data n
  have hhist : history.length = n := by
    simpa [history, onlineMVPActualStackHistory] using
      onlineStackHistory_length
        (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) n
  have htake : history.take n = history := by
    simpa [hhist] using List.take_length history
  change onlineMVPActualPlanningStage E
      (onlineMVPHistoryRowAt hH E fallback history)
      (onlineMVPHistoryNextAt fallback history) history.length h =
    onlineMVPActualPlanningStage E
      (onlineMVPActualStackRowAt hH initial fallback planner data)
      (onlineMVPActualStackNextAt hH initial fallback planner data) n h
  rw [hhist]
  change OnlineObservedPlanningStage.mk (E h)
      (fun s a =>
        onlineMVPSourceBatchList (onlineMVPRowVisitList
          (onlineMVPHistoryRowAt hH E fallback
            history)
          (onlineMVPHistoryNextAt fallback history) n (h, (s, a)))) =
    OnlineObservedPlanningStage.mk (E h)
      (fun s a =>
        onlineMVPSourceBatchList (onlineMVPRowVisitList
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data) n (h, (s, a))))
  congr 1
  funext s a
  congr 1
  rw [onlineMVPRowVisitList_history_eq hH E fallback
    history n (by omega) (h, (s, a)),
    onlineMVPActualStackHistory_rowVisitList]
  rw [htake]

end StatisticalRL.OnlineRL
