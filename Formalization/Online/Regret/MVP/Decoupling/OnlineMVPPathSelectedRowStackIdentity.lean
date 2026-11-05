import Formalization.Online.Regret.MVP.Optimism.MVPBackwardOptimism
import Formalization.Online.Regret.MVP.MVPVarianceDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler

/-! Deterministic selected-row alignment for a path and finite stack with the
same full transcript. -/
namespace StatisticalRL.OnlineRL

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- At each stage and episode, the pair selected from the sequential path is
the state-action component of the corresponding finite-stack row. -/
theorem mvpPathSelectedRow_eq_stackRow_of_transcript
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H))
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback planner data (K * H))
    (h : Fin H) (k : Fin K) :
    onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
      (onlineMVPActualStackRowAt hH initial fallback planner data (k.val * H + h.val)).2 := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  let rowAt := onlineTranscriptRowSequence (choose []) history
  let n := k.val * H + h.val
  have hlen : history.length = K * H := by
    simpa [history] using onlineSequentialPathHistory_length choose (K * H) [] path
  have hn : n < history.length := by
    rw [hlen]
    dsimp [n]
    calc
      k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have htake : history.take n =
      onlineMVPActualStackHistory hH initial fallback planner data n := by
    have hstack : history.take n =
        (onlineMVPActualStackHistory hH initial fallback planner data (K * H)).take n := by
      simpa [history, choose] using congrArg (fun xs => xs.take n) htranscript
    calc
      history.take n =
        (onlineMVPActualStackHistory hH initial fallback planner data (K * H)).take n := hstack
      _ = onlineMVPActualStackHistory hH initial fallback planner data n := by
        simpa [onlineMVPActualStackHistory, choose] using
          onlineStackHistory_take choose (onlineFiniteStackExtend K fallback data)
            (K * H) n (by omega)
  have hcons := onlineSequentialPathHistory_rows_consistent choose (K * H) []
    (by intro j; exact Fin.elim0 j) path
  have hrowRecord : rowAt n = (history.get ⟨n, hn⟩).1 :=
    onlineTranscriptRowSequence_agrees (choose []) history ⟨n, hn⟩
  have hrowChoose : (history.get ⟨n, hn⟩).1 = choose (history.take n) := hcons ⟨n, hn⟩
  calc
    onlineActualStageRowSequence H K hH initial fallback planner path h k.val = (rowAt n).2 := rfl
    _ = ((history.get ⟨n, hn⟩).1).2 := congrArg Prod.snd hrowRecord
    _ = (choose (history.take n)).2 := congrArg Prod.snd hrowChoose
    _ = (onlineMVPActualStackRowAt hH initial fallback planner data n).2 := by
      rw [htake]
      rfl

end StatisticalRL.OnlineRL
