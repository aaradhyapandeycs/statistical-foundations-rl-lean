import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions
import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! Same-history actual selected-row T₂ charge alignment. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t2AlignStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t2AlignActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualT2Point
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  onlineRegretAnalysisCharge H (Real.log (1 / δ)) c₁ c₂ stage U sa.1 sa.2

theorem onlineActualT2_eq_sum_points
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) :
    onlineActualT2 H K hH E initial fallback path δ c₁ c₂ =
      ∑ k : Fin K, ∑ h : Fin H, onlineActualT2Point H K hH E initial fallback path δ c₁ c₂ h k := by
  classical
  unfold onlineActualT2
  apply Finset.sum_congr rfl
  intro k hk
  unfold onlineActualEpisodeRegretTerms
  dsimp only
  apply Finset.sum_bij (fun n hn => ⟨n, Finset.mem_range.mp hn⟩)
  · intro n hn
    exact Finset.mem_univ _
  · intro n hn m hm he
    exact congrArg Fin.val he
  · intro h hh
    exact ⟨h.val, Finset.mem_range.mpr h.isLt, Fin.ext rfl⟩
  · intro n hn
    have hnH : n < H := Finset.mem_range.mp hn
    let h : Fin H := ⟨n, hnH⟩
    have halign := onlineActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
    simp only [onlineCappedEpisodeT2, dif_pos hnH]
    dsimp [onlineActualT2Point, onlineActualOptimisticContinuation, onlineCappedBackwardValueAt]
    rw [halign]
    simp [h, hnH, onlinePreEpisodePlanningStages]
end StatisticalRL.OnlineRL
