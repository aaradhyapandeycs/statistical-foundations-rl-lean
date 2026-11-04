import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Formalization.Online.SourceOptimism.CappedBackwardRecursion
import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Mathlib.Data.List.Range

/-! Definitions of the retained-batch MVP planner from its actual history.
The source uses the corrected power-of-two trigger interpretation (C13)
and the imported finite zero-count capped backup (C8). No independence,
concentration, optimism or source-correspondence field is assumed.
History extraction is totalized only outside its recorded prefix; the
planner consumes exactly the prefix length, with proved access identities.
-/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

section RowLists
variable {Row Outcome : Type*} [DecidableEq Row] [DecidableEq Outcome]
/-- The outcomes observed at row `r` in the first `n` chronological records. -/
def onlineMVPRowVisitList (rowAt : ℕ → Row) (nextAt : ℕ → Outcome)
    (n : ℕ) (r : Row) : List Outcome :=
  ((List.range n).filterMap fun t =>
    if rowAt t = r then some (nextAt t) else none)
end RowLists

section SourceBatch
variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
def onlineMVPSourceBatchStart (n : ℕ) : ℕ :=
  if n < 2 then 0 else onlineMVPStoredCount n

def onlineMVPSourceBatchEnd (n : ℕ) : ℕ :=
  if n < 2 then n else 2 * onlineMVPStoredCount n

/-- The source's threshold-selected last batch is a chronological slice. -/
def onlineMVPSourceBatchList (xs : List Outcome) : List Outcome :=
  (List.take (onlineMVPSourceBatchEnd xs.length) xs).drop
    (onlineMVPSourceBatchStart xs.length)

end SourceBatch

/-- Actual pre-episode MVP stages use exactly the latest committed batch at
each row.  The finite history is supplied as row/successor arrays; every
observation list is computed from those arrays and the proved source slice. -/
noncomputable def onlineMVPActualPlanningStage
    {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
    {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State)
    (n : ℕ) (h : Fin H) : OnlineObservedPlanningStage State Action where
  environment := E h
  observations s a := by
    classical
    exact onlineMVPSourceBatchList
      (onlineMVPRowVisitList rowAt nextAt n (h, (s, a)))

section HistoryPlanner
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance modelStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance modelStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance modelActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Totalized row extraction from a finite actual transcript. The arbitrary
row is used only beyond the transcript length. -/
noncomputable def onlineMVPHistoryRowAt {H : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State)) (n : ℕ) :
    OnlineMDPRow State Action H :=
  if hn : n < history.length then (history.get ⟨n, hn⟩).1
  else (⟨0, hH⟩, (fallback, Classical.choice (E ⟨0, hH⟩).action_nonempty))

/-- Totalized successor extraction from a finite actual transcript. The
fallback is never used on a record that exists. -/
def onlineMVPHistoryNextAt {H : ℕ} (fallback : State)
    (history : List (OnlineMDPRow State Action H × State)) (n : ℕ) : State :=
  if hn : n < history.length then (history.get ⟨n, hn⟩).2 else fallback

/-- The MVP planning table computed from a completed observed prefix, using
the retained source dyadic batches. -/
noncomputable def onlineMVPHistoryPlanningStages {H : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State)) :
    List (OnlineObservedPlanningStage State Action) :=
  let rowAt := onlineMVPHistoryRowAt hH E fallback history
  let nextAt := onlineMVPHistoryNextAt fallback history
  List.ofFn (fun h : Fin H =>
    letI : Nonempty State := (E h).state_nonempty
    onlineMVPActualPlanningStage E rowAt nextAt history.length h)

/-- A fixed deterministic maximizing rule computed from the source MVP
retained-batch planning table. `onlineEpisodicChoose` feeds it only completed
episodes and supplies the stage-clock state/action context. -/
noncomputable def onlineMVPCommittedGreedyPlanner {H : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) : OnlineEpisodePlanner State Action H :=
  fun history h s =>
    letI : Nonempty Action := (E h).action_nonempty
    Classical.choose (EnvironmentStage.exists_maximizer
      (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlineMVPHistoryPlanningStages hH E fallback history) h.val s))

end HistoryPlanner
end StatisticalRL.OnlineRL
