import Formalization.Online.Regret.W1.OnlineW1ActualRowRank
import Formalization.Online.Regret.W1.OnlineW1AllRowsHarmonic

/-! OnlineW1ActualCountBudget: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1ActualCountBudgetDraftStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1ActualCountBudgetDraftActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineSequential_reciprocalCount_budget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) :
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length : ℝ)⁻¹) ≤
      (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * (1 + Real.log (K + 1 : ℝ)) := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  change (∑ h : Fin H, ∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length : ℝ)⁻¹) ≤ _
  have hstage : ∀ h : Fin H, (∑ k : Fin K,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length : ℝ)⁻¹) ≤
      (Fintype.card (State × Action) : ℝ) * (1 + Real.log (K + 1 : ℝ)) := by
    intro h
    let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
    have heq : (∑ k : Fin K,
      ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length : ℝ)⁻¹) =
      ∑ k : Fin K, (onlineVisitCount rows k.val (rows k.val) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [onlineSequential_playedRow_count_eq_rank H K hH E initial fallback planner path k h]
    rw [heq]
    have hsum : (∑ k : Fin K, (onlineVisitCount rows k.val (rows k.val) : ℝ)⁻¹) =
        ∑ j ∈ Finset.range K, (onlineVisitCount rows j (rows j) : ℝ)⁻¹ := by
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
    exact onlineVisitCount_allRows_reciprocal_le rows K
  calc
    _ ≤ ∑ _h : Fin H, ((Fintype.card (State × Action) : ℝ) * (1 + Real.log (K + 1 : ℝ))) :=
      Finset.sum_le_sum (fun h _ => hstage h)
    _ = _ := by simp [Fintype.card_prod]; ring
end StatisticalRL.OnlineRL
