import Formalization.Online.Regret.MVP.MVPT2Definitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualPlanningAdapter
import Formalization.Online.Regret.MVP.Model.OnlineMVPRowDyadicBatch
import Formalization.Online.Regret.MVP.OnlineMVPAllRowsBudget

/-! Retained-count bridge from actual sequential history to retained-count budget.
The planner is arbitrary: the MVP planner is a direct specialization. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpT2CountStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpT2CountActionDecidable : DecidableEq Action := Classical.decEq Action


theorem mvpT2_actual_retainedCount_eq_rank
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K*H)) (h : Fin H) (k : Fin K) :
    mvpT2ActualRetainedCount H K hH E initial fallback planner path h k =
      onlineMVPStoredCount (onlineVisitCount
        (onlineActualStageRowSequence H K hH initial fallback planner path h) k.val
        (onlineActualStageRowSequence H K hH initial fallback planner path h k.val)) := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K*H) [] path
  let hist := history.take (k.val*H)
  let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
  have hlen : hist.length = k.val*H := by
    have hh := onlineSequentialPathHistory_length choose (K*H) [] path
    have hk : k.val*H ≤ K*H := Nat.mul_le_mul_right H k.isLt.le
    simp [hist, history, hh, List.length_take, Nat.min_eq_left hk]
  unfold mvpT2ActualRetainedCount onlineMVPActualPlanningStage
  change (onlineMVPSourceBatchList (onlineMVPRowVisitList
    (onlineMVPHistoryRowAt hH E fallback hist) (onlineMVPHistoryNextAt fallback hist)
    hist.length (h, rows k.val))).length = _
  rw [onlineMVPSourceBatchList_length,
    onlineMVPRowVisitList_history_eq hH E fallback hist hist.length le_rfl,
    List.take_length]
  exact congrArg onlineMVPStoredCount
    (onlineSequential_playedRow_count_eq_rank H K hH E initial fallback planner path k h)

theorem mvpT2_actual_retainedReciprocal_budget
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K*H)) :
    (∑ h : Fin H, ∑ k : Fin K,
      (((max (mvpT2ActualRetainedCount H K hH E initial fallback planner path h k) 1 : ℕ) : ℝ)⁻¹)) ≤
      4 * (Fintype.card State : ℝ) * Fintype.card Action * H * (Real.log K / Real.log 2) := by
  classical
  have hstage (h : Fin H) :
      (∑ k : Fin K,
        (((max (mvpT2ActualRetainedCount H K hH E initial fallback planner path h k) 1 : ℕ) : ℝ)⁻¹)) ≤
        (Fintype.card (State × Action) : ℝ) * (4 * (Real.log K / Real.log 2)) := by
    let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
    have heq : (∑ k : Fin K,
        (((max (mvpT2ActualRetainedCount H K hH E initial fallback planner path h k) 1 : ℕ) : ℝ)⁻¹)) =
        ∑ k ∈ Finset.range K, onlineMVPStoredReciprocal (onlineVisitCount rows k (rows k)) := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mvpT2_actual_retainedCount_eq_rank]
      rfl
    rw [heq]
    exact onlineMVP_allRows_reciprocal_le rows K hK
  calc
    _ ≤ ∑ _h : Fin H, ((Fintype.card (State × Action) : ℝ) * (4 * (Real.log K / Real.log 2))) :=
      Finset.sum_le_sum (fun h _ => hstage h)
    _ = _ := by simp [Fintype.card_prod]; ring
end StatisticalRL.OnlineRL
