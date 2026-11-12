import Formalization.Online.SourceOptimism.GreedySequentialBellmanOptimism

/-! Consume actual finite-trajectory optimal V/Q
exports and real sequential history prefixes. No source delta-prime arithmetic
or new law/coupling claim is introduced. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineGreedyTrajectoryStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- Actual trajectory values of one true optimal policy at every suffix. Q is
a forced-initial-action trajectory return, even off the policy's chosen action. -/
def onlineHistoryAllStageTrajectoryOptimism
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ h : Fin H,
    (∀ s, DecisionStage.trajectoryValue
        ((EnvironmentStage.greedyStages (List.ofFn E)).drop h.val) s ≤
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val s) ∧
    (∀ s a, DecisionStage.trajectoryQ
        ((EnvironmentStage.greedyStages (List.ofFn E)).drop h.val) s a ≤
      onlineCappedBackwardQAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val s a)

/-- A realized sequential transcript has exactly kH completed transitions at
its episode-k boundary. This includes the final transition of each past episode. -/
theorem onlineSequential_episodePrefix_length
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : ℕ) (hk : k ≤ K) :
    ((onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path).take
        (k * H)).length = k * H := by
  have hlen := onlineSequentialPathHistory_length
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hbound : k * H ≤ K * H := Nat.mul_le_mul_right H hk
  simpa only [List.length_take, List.length_nil, zero_add,
    hlen, Nat.min_eq_left hbound]

/-- Every actual action uses the fixed episode planner on the full history's
completed-episode prefix. This is a pathwise statement from row consistency;
it does not condition on a random visit count. -/
theorem onlineSequential_actualAction_completedPrefix
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    ∀ j : Fin history.length,
      (history.get j).1.2.2 = planner (history.take ((j.val / H) * H))
        ⟨j.val % H, Nat.mod_lt _ hH⟩
        (onlineEpisodicCurrentState H K initial fallback (history.take j.val)) := by
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  have hrows : onlineTranscriptRowsConsistent choose history :=
    onlineSequentialPathHistory_rows_consistent choose (K * H) []
      (by intro j; exact Fin.elim0 j) path
  dsimp only
  intro j
  change Fin history.length at j
  have hj : (history.take j.val).length = j.val := by
    simp only [List.length_take, Nat.min_eq_left j.isLt.le]
  have hfloor : j.val / H * H ≤ j.val := Nat.div_mul_le_self _ _
  have h := congrArg (fun row : OnlineMDPRow State Action H => row.2.2) (hrows j)
  simpa only [choose, onlineEpisodicChoose, hj, List.take_take,
    Nat.min_eq_left hfloor, Nat.min_eq_right hfloor] using h

/-- Actual-law trajectory optimism with the same causal greedy planner and
strict factor-2 confidence. Source delta-prime/cardinality normalization is
intentionally left separate, as is any mutable-implementation simulation. -/
theorem onlineGreedySequential_allStageTrajectoryOptimism_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 2 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K * H) [] sample.2)} := by
  simpa only [onlineHistoryAllStageTrajectoryOptimism, onlineHistoryAllStageBellmanOptimism,
    EnvironmentStage.greedy_suffix_value, EnvironmentStage.greedy_suffix_Q] using
      onlineGreedySequential_allStageBellmanOptimism_strict H K hH hK E ρ
        fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂

end StatisticalRL.OnlineRL
