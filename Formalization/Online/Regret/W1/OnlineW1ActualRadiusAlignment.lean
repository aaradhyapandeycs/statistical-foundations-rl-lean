import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! OnlineW1ActualRadiusAlignment: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1ActualRadiusAlignmentLocalInstance1 : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1ActualRadiusAlignmentLocalInstance2 : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualW1Count
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℕ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
  (onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length

noncomputable def onlineActualW1Variance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
  let sa := rows k.val
  ((E h).transition sa.1 sa.2).variance (onlineTrueSuffixRowFamily E (h, sa))

noncomputable def onlineActualW1RadiusTerm
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
  let sa := rows k.val
  let n := onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ h k
  if 3 ≤ n then onlineTrueW1Radius H δ n ((E h).transition sa.1 sa.2)
    (onlineTrueSuffixRowFamily E (h, sa)) else H

/-- The radius array is exactly the radius sum in the actual episode
certificate, not a separately sampled or counterfactual row. -/
theorem onlineActualEpisodeW1RadiusSum_eq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) :
    onlineActualEpisodeW1RadiusSum H K hH E initial fallback path k δ c₁ c₂ =
      ∑ h : Fin H, onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ h k := by
  classical
  unfold onlineActualEpisodeW1RadiusSum
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
    simp only [dif_pos hnH]
    dsimp [onlineActualW1RadiusTerm, onlineActualW1Count]
    rw [halign]
    simp [h, hnH]
end StatisticalRL.OnlineRL
