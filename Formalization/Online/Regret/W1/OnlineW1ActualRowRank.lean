import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.W1.OnlineW1ActualEpisodeCount
import Formalization.Online.Regret.W1.OnlineW1AllRowsSmallCount

/-! OnlineW1ActualRowRank: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1ActualRowRankDraftStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1ActualRowRankDraftActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The actual observed count before episode k of the row played at stage h
is precisely its strict-past episode visit rank. -/
theorem onlineSequential_playedRow_count_eq_rank
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
    (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length =
      onlineVisitCount rows k.val (rows k.val) := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  let rowAt := onlineTranscriptRowSequence (choose []) history
  let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
  have hlen : history.length = K * H := by
    simpa [history] using onlineSequentialPathHistory_length choose (K * H) [] path
  have hrows : ∀ j : Fin history.length, rowAt j.val = (history.get j).1 := by
    intro j
    exact onlineTranscriptRowSequence_agrees _ _ _
  have hrcons : onlineTranscriptRowsConsistent choose history :=
    onlineSequentialPathHistory_rows_consistent choose (K * H) [] (by intro j; exact Fin.elim0 j) path
  have htag : ∀ e, e < K → (rowAt (e * H + h.val)).1 = h := by
    intro e he
    have hj : e * H + h.val < history.length := by
      rw [hlen]
      calc
        e * H + h.val < e * H + H := Nat.add_lt_add_left h.isLt _
        _ = (e + 1) * H := by rw [Nat.succ_mul]
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt he)
    have ht := onlineEpisodicTranscript_stage H K hH initial fallback planner history hrcons
      rowAt hrows ⟨e * H + h.val, hj⟩
    apply Fin.ext
    simpa [Nat.add_mod, Nat.mul_comm, Nat.mod_eq_of_lt h.isLt] using ht
  have hbridge := onlineSequential_observedCount_eq_stageVisitRank H K hH E initial fallback
    planner path k h (h, rows k.val) rfl
  change (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length =
    onlineVisitCount (fun e => rowAt (e * H + h.val)) k.val (h, rows k.val) at hbridge
  change (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length =
    onlineVisitCount rows k.val (rows k.val)
  rw [hbridge]
  unfold onlineVisitCount
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨he, heq⟩
    refine ⟨he, ?_⟩
    have hh := congrArg (fun p : OnlineMDPRow State Action H => p.2) heq
    change rows e = rows k.val at hh
    exact hh
  · rintro ⟨he, heq⟩
    have heK : e < K := he.trans k.isLt
    have hstage := htag e heK
    refine ⟨he, ?_⟩
    apply Prod.ext
    · exact hstage
    · exact heq
/-- Across all stages and episodes, at most three visits per state-action
row and stage have an observed pre-episode count below three. -/
theorem onlineSequential_lowCount_visits_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 3
        then (1 : ℝ) else 0) ≤
      3 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  change (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 3
        then (1 : ℝ) else 0) ≤ _
  have hstage : ∀ h : Fin H, (∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 3
        then (1 : ℝ) else 0) ≤ 3 * (Fintype.card (State × Action) : ℝ) := by
    intro h
    let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
    have heq : (∑ k : Fin K,
      if (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length < 3
        then (1 : ℝ) else 0) =
      ∑ k : Fin K, if onlineVisitCount rows k.val (rows k.val) < 3 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [onlineSequential_playedRow_count_eq_rank H K hH E initial fallback planner path k h]
    rw [heq]
    have hsum : (∑ k : Fin K, if onlineVisitCount rows k.val (rows k.val) < 3 then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range K, if onlineVisitCount rows j (rows j) < 3 then (1 : ℝ) else 0 := by
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
    exact onlineVisitCount_allRows_lowCount_le rows K
  calc
    _ ≤ ∑ _h : Fin H, (3 * (Fintype.card (State × Action) : ℝ)) :=
      Finset.sum_le_sum (fun h _ => hstage h)
    _ = _ := by simp [Fintype.card_prod]; ring
end StatisticalRL.OnlineRL
