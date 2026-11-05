import Formalization.Online.Regret.MVP.Main.MVPActualRegret
import Formalization.Online.Regret.MVP.Main.MVPActualEpisodeTelescope
import Formalization.Online.Regret.MVP.Optimism.MVPSourceOptimismStatement

/-! actual MVP regret decomposition under the actual optimism event.
The fluctuation terms are not assumed centered or bounded. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpRegretStage (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) : OnlineObservedPlanningStage State Action :=
  let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H)
  letI : Nonempty State := (E h).state_nonempty
  onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
    (onlineMVPHistoryNextAt fallback hist) hist.length h

noncomputable def mvpRegretState (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) : State :=
  onlineEpisodicCurrentState H K initial fallback
    ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H+n))

noncomputable def mvpRegretAction (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) : Action :=
  if hn : n<H then onlineT4PlayedAction H K hH initial fallback
    (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) path k ⟨n,hn⟩
  else Classical.choice ((E ⟨0,hH⟩).action_nonempty)

noncomputable def mvpRegretEmpiricalSum (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ k : Fin K, ∑ h : Fin H, onlineCappedEpisodeT1 H
    (mvpRegretStage H K hH E initial fallback path δ c₁ c₂ k)
    (mvpRegretState H K hH E initial fallback path δ c₁ c₂ k)
    (mvpRegretAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1/δ)) c₁ c₂ h.val
noncomputable def mvpRegretChargeSum (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ k : Fin K, ∑ h : Fin H, onlineCappedEpisodeT2 H
    (mvpRegretStage H K hH E initial fallback path δ c₁ c₂ k)
    (mvpRegretState H K hH E initial fallback path δ c₁ c₂ k)
    (mvpRegretAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1/δ)) c₁ c₂ h.val
noncomputable def mvpRegretTransitionSum (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ k : Fin K, ∑ h : Fin H, onlineCappedEpisodeT3 H
    (mvpRegretStage H K hH E initial fallback path δ c₁ c₂ k)
    (mvpRegretState H K hH E initial fallback path δ c₁ c₂ k)
    (mvpRegretAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1/δ)) c₁ c₂ h.val

theorem mvpActualRegret_le_decomposition_of_optimism
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδsmall : δ≤1/100) (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂)
    (hopt : mvpHistoryAllStageOptimism (K := K) hH E fallback δ c₁ c₂
      (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂)) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂) ≤
      mvpRegretEmpiricalSum H K hH E initial fallback path δ c₁ c₂ +
      mvpRegretChargeSum H K hH E initial fallback path δ c₁ c₂ +
      mvpRegretTransitionSum H K hH E initial fallback path δ c₁ c₂ +
      (∑ k : Fin K, onlineT4EpisodeIncrement H K hH E initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) path k) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  let stage := fun k => mvpRegretStage H K hH E initial fallback path δ c₁ c₂ k
  let state := fun k => mvpRegretState H K hH E initial fallback path δ c₁ c₂ k
  let action := fun k => mvpRegretAction H K hH E initial fallback path δ c₁ c₂ k
  let reward := fun k (h : Fin H) => (E h).reward (state k h.val) (action k h.val)
  let charge := fun k (h : Fin H) => onlineCappedEpisodeT2 H (stage k) (state k) (action k) (Real.log (1/δ)) c₁ c₂ h.val
  let error := fun k (h : Fin H) => onlineCappedEpisodeT1 H (stage k) (state k) (action k) (Real.log (1/δ)) c₁ c₂ h.val
  let noise := fun k (h : Fin H) => onlineCappedEpisodeT3 H (stage k) (state k) (action k) (Real.log (1/δ)) c₁ c₂ h.val
  let opt := fun (_k : Fin K) => EnvironmentStage.optimalValue (List.ofFn E)
  let estimate := fun (k : Fin K) => onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
    (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) 0
  let policy := fun (k : Fin K) => onlineT4SelectedEpisodeValue H hH E planner history k.val
  have hreset (k : Fin K) : state k 0 = initial k := by
    have hl := onlineSequential_episodePrefix_length H K hH E initial fallback planner path k.val k.isLt.le
    have hr := onlineEpisodicCurrentState_reset H K hH initial fallback (history.take (k.val*H)) k hl
    simpa [state,mvpRegretState,history,mvpVarianceHistory,planner] using hr
  have hopt' (k : Fin K) : opt k (initial k) ≤ estimate k (initial k) := by
    have h := (hopt k ⟨0,hH⟩).1 (initial k)
    simpa [opt,estimate,history] using h
  have htel (k : Fin K) : estimate k (initial k) ≤
      ∑ h : Fin H, (reward k h + charge k h + error k h + noise k h) := by
    have h := mvpActualEpisode_realized_telescope H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ k
    change onlineCappedEpisodeValueAlongPath (stage k) (state k) H (Real.log (1/δ)) c₁ c₂ 0 ≤ _ at h
    rw [Finset.sum_range] at h
    have hstart : onlineCappedEpisodeValueAlongPath (stage k) (state k) H (Real.log (1/δ)) c₁ c₂ 0 = estimate k (initial k) := by
      change onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ (List.ofFn (stage k)) (state k 0) = _
      rw [hreset k]
      rfl
    rw [hstart] at h
    calc
      _ ≤ ∑ j : Fin H, onlineCappedEpisodeTelescopeSummand H (stage k) (state k) (action k) (Real.log (1/δ)) c₁ c₂ j.val := h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [reward,charge,error,noise,onlineCappedEpisodeTelescopeSummand,
          onlineCappedEpisodeT1,onlineCappedEpisodeT2,onlineCappedEpisodeT3, dif_pos j.isLt]
        rfl
  have h := onlineRegret_le_T1_T2_T3_T4 H K initial opt estimate policy reward charge error noise hopt' htel
  have hreturn (k : Fin K) : (∑ h : Fin H, reward k h) =
      onlineT4EpisodeReturn H K hH E initial fallback planner path k := by
    unfold onlineT4EpisodeReturn
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro h hh
    simp [reward,state,action,mvpRegretState,mvpRegretAction,onlineT4EpisodeState,h.isLt,history,mvpVarianceHistory,planner]
  simp_rw [hreturn] at h
  simpa only [mvpActualEpisodeRegret,mvpRegretEmpiricalSum,mvpRegretChargeSum,mvpRegretTransitionSum,
    onlineT4EpisodeIncrement,planner,history,opt,policy,charge,error,noise,stage,state,action] using h
end StatisticalRL.OnlineRL
