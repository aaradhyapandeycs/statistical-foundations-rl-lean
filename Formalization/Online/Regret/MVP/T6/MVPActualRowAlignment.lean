import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions
import Formalization.Online.Regret.Telescope
import Formalization.Online.Regret.W1.OnlineW1ActualCountBudget

/-! OnlineW1ActualRowAlignment: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualRowAlignment_mvpRowAlignState : DecidableEq State := Classical.decEq State
noncomputable local instance t6MVPActualRowAlignment_mvpRowAlignAction : DecidableEq Action := Classical.decEq Action

/-- The stage row used in rank bookkeeping is the actual state and action
used in the episode W₁ term, on the same path. -/
theorem mvpActualStageRow_eq_episodeStateAction
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (δ' c₁ c₂ : ℝ) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ')) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
      (state h.val, action h.val) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ')) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let prehist := history.take (k.val * H)
  let stage : Fin H → OnlineObservedPlanningStage State Action :=
    fun h => onlineHistoryPlanningStage E prehist h
  let state : ℕ → State := fun n =>
    onlineEpisodicCurrentState H K initial fallback
      (history.take (k.val * H + n))
  let action : ℕ → Action := fun n =>
    if hn : n < H then
      (history.get ⟨k.val * H + n, by
        have hlen := onlineSequentialPathHistory_length
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
        rw [hlen]
        simp only [List.length_nil, zero_add]
        calc
          k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
    else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
  change onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
    (state h.val, action h.val)
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let rowAt := onlineTranscriptRowSequence (choose []) history
  have hj : k.val * H + h.val < history.length := by
    have hl : history.length = K * H := by
      simpa [history, choose] using onlineSequentialPathHistory_length choose (K * H) [] path
    rw [hl]
    calc
      k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have henumerate : rowAt (k.val * H + h.val) =
      (history.get ⟨k.val * H + h.val, hj⟩).1 := by
    change onlineTranscriptRowSequence (choose []) history
      (k.val * H + h.val) = (history.get ⟨k.val * H + h.val, hj⟩).1
    exact onlineTranscriptRowSequence_agrees (choose []) history ⟨k.val * H + h.val, hj⟩
  have hrow := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
  change (history.get ⟨k.val * H + h.val, hj⟩).1 =
    (h, (state h.val, planner prehist h (state h.val))) at hrow
  have hstate : (rowAt (k.val * H + h.val)).2.1 = state h.val := by
    rw [henumerate, hrow]
  have haction : (rowAt (k.val * H + h.val)).2.2 = action h.val := by
    rw [henumerate]
    simp [action, h.isLt]
  change (rowAt (k.val * H + h.val)).2 = (state h.val, action h.val)
  exact Prod.ext hstate haction
end StatisticalRL.OnlineRL
