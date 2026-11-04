import Formalization.Online.Regret.W1.OnlineW1ActualRowRank

/-! Each played row has at most one zero-count visit. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
theorem onlineT2_firstVisit_perRow_le {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (r : Row) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ onlineVisitCount rowAt j r < 1 then (1 : ℝ) else 0) ≤ 1 := by
  classical
  have h := onlineVisitCount_sum_by_rank rowAt K r (fun n => if n < 1 then (1 : ℝ) else 0)
  have hcard : ((Finset.range (onlineVisitCount rowAt K r)).filter (fun n => n < 1)).card ≤ 1 := by
    calc
      _ ≤ (Finset.range 1).card := Finset.card_le_card (by
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
      _ = 1 := Finset.card_range 1
  have hsum : (∑ n ∈ Finset.range (onlineVisitCount rowAt K r),
      if n < 1 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hn : 0 < onlineVisitCount rowAt K r
    · simp [Finset.sum_ite, hn]
    · have hz : onlineVisitCount rowAt K r = 0 := by omega
      simp [hz]
  have heq : (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ onlineVisitCount rowAt j r < 1 then (1 : ℝ) else 0) =
      ∑ n ∈ Finset.range (onlineVisitCount rowAt K r), if n < 1 then (1 : ℝ) else 0 := by
    simpa only [ite_and] using h
  exact heq ▸ hsum

theorem onlineT2_firstVisit_allRows_le {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) :
    (∑ j ∈ Finset.range K,
      if onlineVisitCount rowAt j (rowAt j) < 1 then (1 : ℝ) else 0) ≤
      1 * Fintype.card Row := by
  classical
  have heq : (∑ j ∈ Finset.range K,
      if onlineVisitCount rowAt j (rowAt j) < 1 then (1 : ℝ) else 0) =
      ∑ r : Row, ∑ j ∈ Finset.range K,
        if rowAt j = r ∧ onlineVisitCount rowAt j r < 1 then (1 : ℝ) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ite_and, Finset.sum_ite_eq']
  rw [heq]
  calc
    _ ≤ ∑ _r : Row, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact onlineT2_firstVisit_perRow_le rowAt K r
    _ = 1 * Fintype.card Row := by simp

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t2FirstStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t2FirstActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineSequential_T2_firstVisits_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 1
        then (1 : ℝ) else 0) ≤
      1 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  change (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 1
        then (1 : ℝ) else 0) ≤ _
  have hstage : ∀ h : Fin H, (∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 1
        then (1 : ℝ) else 0) ≤ 1 * (Fintype.card (State × Action) : ℝ) := by
    intro h
    let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
    have heq : (∑ k : Fin K,
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 1
        then (1 : ℝ) else 0) =
      ∑ k : Fin K, if onlineVisitCount rows k.val (rows k.val) < 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [onlineSequential_playedRow_count_eq_rank H K hH E initial fallback planner path k h]
    rw [heq]
    have hsum : (∑ k : Fin K, if onlineVisitCount rows k.val (rows k.val) < 1 then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range K, if onlineVisitCount rows j (rows j) < 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_bij (fun k _ => k.val)
      · intro k hk
        exact Finset.mem_range.mpr k.isLt
      · intro k hk l hl he
        exact Fin.ext he
      · intro j hj
        exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
      · intro k hk
        rfl
    rw [hsum]
    exact onlineT2_firstVisit_allRows_le rows K
  calc
    _ ≤ ∑ _h : Fin H, (1 * (Fintype.card (State × Action) : ℝ)) :=
      Finset.sum_le_sum (fun h _ => hstage h)
    _ = _ := by simp [Fintype.card_prod]; ring
end StatisticalRL.OnlineRL
