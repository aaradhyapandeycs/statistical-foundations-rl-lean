import Formalization.Online.Regret.MVP.Main.MVPActualRegretDecomposition
import Formalization.Online.Regret.MVP.T34.MVPJointSource

/-! alignment of actual regret components with the proved
T2/T3/T4/W4 quantities, on one realized history. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpRegret_components_align
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) :
    mvpRegretEmpiricalSum H K hH E initial fallback path δ c₁ c₂ ≤
      mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ ∧
    mvpRegretChargeSum H K hH E initial fallback path δ c₁ c₂ =
      mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ ∧
    mvpRegretTransitionSum H K hH E initial fallback path δ c₁ c₂ =
      mvpActualT3 H K hH E initial fallback path δ c₁ c₂ ∧
    (∑ k : Fin K, onlineT4EpisodeIncrement H K hH E initial fallback
      (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) path k) =
      mvpActualT4 H K hH E initial fallback path (Real.log (1/δ)) c₁ c₂ := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  have hrow (k : Fin K) (h : Fin H) :
      onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
        (mvpRegretState H K hH E initial fallback path δ c₁ c₂ k h.val,
         mvpRegretAction H K hH E initial fallback path δ c₁ c₂ k h.val) := by
    have hr := mvpActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
    simpa [planner,history,mvpVarianceHistory,mvpRegretState,mvpRegretAction,onlineT4PlayedAction,h.isLt] using hr
  have htail (k : Fin K) (h : Fin H) :
      mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k =
        onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
          ((List.ofFn (mvpRegretStage H K hH E initial fallback path δ c₁ c₂ k)).drop (h.val+1)) := by
    rfl
  have hsucc (k : Fin K) (h : Fin H) :
      mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
        (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k) =
      onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
        ((List.ofFn (mvpRegretStage H K hH E initial fallback path δ c₁ c₂ k)).drop (h.val+1))
        (mvpRegretState H K hH E initial fallback path δ c₁ c₂ k (h.val+1)) := by
    have hs := mvpActualSuccessor_value_eq_episode_next H K hH E initial fallback path δ c₁ c₂ h k
    simpa only [mvpRegretStage,mvpRegretState,onlineMVPHistoryPlanningStages] using hs
  constructor
  · unfold mvpRegretEmpiricalSum mvpVarianceW4
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro h hh
    apply Finset.sum_le_sum
    intro k hk
    simp only [onlineCappedEpisodeT1,dif_pos h.isLt]
    rw [hrow k h, htail k h]
    simp only [mvpRegretStage, Prod.fst, Prod.snd]
    exact le_max_left _ _
  constructor
  · unfold mvpRegretChargeSum mvpVarianceT2
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro k hk
    simp only [onlineCappedEpisodeT2,dif_pos h.isLt]
    rw [hrow k h, htail k h]
    rfl
  constructor
  · unfold mvpRegretTransitionSum mvpActualT3
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro k hk
    simp only [onlineCappedEpisodeT3,dif_pos h.isLt]
    rw [hrow k h, hsucc k h, htail k h]
    rfl
  · rfl
end StatisticalRL.OnlineRL
