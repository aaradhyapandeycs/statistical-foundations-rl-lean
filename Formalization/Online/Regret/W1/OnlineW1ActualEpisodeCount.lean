import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Formalization.Online.SourceOptimism.GreedySequentialTrajectoryOptimism

/-! OnlineW1ActualEpisodeCount: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1ActualEpisodeCountDraftStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1ActualEpisodeCountDraftActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The observed pre-episode count is the strict-past episode visit rank at
that stage, on the very same realized sequential path and planner. -/
theorem onlineSequential_observedCount_eq_stageVisitRank
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (r : OnlineMDPRow State Action H) (hr : r.1 = h) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    let rowAt := onlineTranscriptRowSequence (choose []) history
    (onlineRowOutcomes (history.take (k.val * H)) r).length =
      onlineVisitCount (fun e => rowAt (e * H + h.val)) k.val r := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  let rowAt := onlineTranscriptRowSequence (choose []) history
  have hlen : history.length = K * H := by
    simpa [history] using onlineSequentialPathHistory_length choose (K * H) [] path
  have hrows : ∀ j : Fin history.length, rowAt j.val = (history.get j).1 := by
    intro j
    exact onlineTranscriptRowSequence_agrees _ _ _
  have hrcons : onlineTranscriptRowsConsistent choose history :=
    onlineSequentialPathHistory_rows_consistent choose (K * H) [] (by intro j; exact Fin.elim0 j) path
  have hstage : ∀ j, j < k.val * H → (rowAt j).1.val = j % H := by
    intro j hj
    have hj' : j < history.length := by
      rw [hlen]
      exact hj.trans_le (Nat.mul_le_mul_right H k.isLt.le)
    exact onlineEpisodicTranscript_stage H K hH initial fallback planner history hrcons
      rowAt hrows ⟨j, hj'⟩
  have hk : k.val * H ≤ history.length := by
    rw [hlen]
    exact Nat.mul_le_mul_right H k.isLt.le
  exact onlineObserved_stage_episode_count_eq history rowAt h k.val hH hk r hr hrows hstage
end StatisticalRL.OnlineRL
