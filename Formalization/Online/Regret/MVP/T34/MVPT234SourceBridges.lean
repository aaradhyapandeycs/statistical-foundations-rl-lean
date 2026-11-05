import Formalization.Online.Regret.MVP.T34.MVPJointSource
import Formalization.Online.Regret.MVP.T6.MVPActualRowAlignment
import Mathlib.Data.List.GetD

/-! Source-expression identities for the actual successor, T3 residual and frozen-policy T4 return. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpT234_successor_eq_getD
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) :
    mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k =
      ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).map Prod.snd).getD
        (k.val*H+h.val) fallback := by
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  have hlen : history.length = K*H := by
    dsimp [history,mvpVarianceHistory]
    simpa using onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂)) (K*H) [] path
  have hi : k.val*H+h.val < history.length := by
    rw [hlen]
    calc
      k.val*H+h.val < k.val*H+H := Nat.add_lt_add_left h.isLt _
      _ = (k.val+1)*H := by rw [Nat.add_mul, one_mul]
      _ ≤ K*H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  change mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k =
    (history.map Prod.snd).getD (k.val*H+h.val) fallback
  rw [List.getD_eq_getElem (history.map Prod.snd) fallback (by simpa using hi), List.getElem_map]
  rfl

theorem mvpT234_T3_eq_expanded
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) :
    mvpActualT3 H K hH E initial fallback path δ c₁ c₂ =
      ∑ h : Fin H, ∑ k : Fin K,
        let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
        let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
        let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
        ((E h).transition sa.1 sa.2).expectation U -
          U (((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).map Prod.snd).getD
            (k.val*H+h.val) fallback) := by
  unfold mvpActualT3
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  rw [mvpT234_successor_eq_getD]

theorem mvpT234_T4_eq_expanded
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) :
    mvpActualT4 H K hH E initial fallback path (Real.log (1/δ)) c₁ c₂ =
      ∑ k : Fin K,
        ((∑ h : Fin H,
          let sa := onlineActualStageRowSequence H K hH initial fallback
            (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) path h k.val
          (E h).reward sa.1 sa.2) -
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H => (E h).withPolicy (fun s => EnvironmentStage.pointMass
            (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
              ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H)) h s)))) (initial k)) := by
  classical
  unfold mvpActualT4
  apply Finset.sum_congr rfl
  intro k hk
  unfold onlineT4EpisodeIncrement onlineT4SelectedEpisodeValue
  dsimp only
  rw [onlineT4SelectedStages_eq_fixed]
  congr 1
  unfold onlineT4EpisodeReturn
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [dif_pos h.isLt]
  have hr := mvpActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
  simpa only [onlineT4EpisodeState, onlineT4PlayedAction, mvpVarianceHistory, h.isLt, dif_pos] using congrArg (fun sa => (E h).reward sa.1 sa.2) hr.symm
end StatisticalRL.OnlineRL
