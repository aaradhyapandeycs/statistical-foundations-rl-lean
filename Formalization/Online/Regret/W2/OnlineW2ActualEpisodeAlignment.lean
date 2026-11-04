import Formalization.Online.Regret.W2.OnlineW2ObservedPointwise
import Formalization.Online.Regret.W2.OnlineW2GapVariance
import Formalization.Online.Regret.W1.OnlineW1ActualRadiusAlignment

/-! Actual episode/stage indexing for W₂, on the same history and planner.
The alignment uses the same actual sequential path. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w2AlignStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w2AlignActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The adaptive gap U−V* on the actual pre-episode history. -/
noncomputable def onlineActualW2Gap
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : State → ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  fun s => U s - onlineTrueSuffixRowFamily E (h, sa) s

/-- W₂ pointwise term using the stage-tagged row and the actual pre-episode
empirical row. -/
noncomputable def onlineActualW2Point
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let gap := onlineActualW2Gap H K hH E initial fallback path δ c₁ c₂ h k
  (onlineObservedPlanningRow stage sa.1 sa.2).expectation gap -
    ((E h).transition sa.1 sa.2).expectation gap

/-- Align the source episode term with its actual stage-indexed points. -/
theorem onlineActualEpisodeW2_eq_sum_points
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) :
    onlineActualEpisodeW2 H K hH E initial fallback path k δ c₁ c₂ =
      ∑ h : Fin H, onlineActualW2Point H K hH E initial fallback path δ c₁ c₂ h k := by
  classical
  unfold onlineActualEpisodeW2
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
    simp only [onlineEpisodeFixedOptimalW2, dif_pos hnH]
    dsimp [onlineActualW2Point, onlineActualW2Gap, onlineActualOptimisticContinuation,
      onlineCappedBackwardValueAt]
    rw [halign]
    simp [h, hnH, onlinePreEpisodePlanningStages, onlineTrueSuffixRowFamily,
      onlineFixedOptimalContinuation, EnvironmentStage.greedy_suffix_value, onlineHistoryPlanningStage]
end StatisticalRL.OnlineRL
