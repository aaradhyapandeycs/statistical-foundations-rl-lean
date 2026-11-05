import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions
import Formalization.Online.Regret.T4.OnlineRegretT4Range

/-! actual MVP regret and the unconditional K H bound. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpActualEpisodeRegret (H K : ℕ) (hH : 0<H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K*H)) (k : Fin K) (δ c₁ c₂ : ℝ) : ℝ :=
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  EnvironmentStage.optimalValue (List.ofFn E) (initial k) -
    onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k)

theorem mvpActualEpisodeRegret_le_horizon (H K : ℕ) (hH : 0<H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K*H)) (k : Fin K) (δ c₁ c₂ : ℝ) :
    mvpActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂ ≤ H := by
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  let g := planner (history.take (k.val*H))
  have hopt : EnvironmentStage.optimalValue (List.ofFn E) (initial k) ≤ H := by
    rw [← EnvironmentStage.greedy_trajectoryValue, DecisionStage.trajectoryValue_eq_backwardValue]
    have hlen (es : List (EnvironmentStage State Action)) :
        (EnvironmentStage.greedyStages es).length = es.length := by
      induction es with
      | nil => rfl
      | cons e es ih => simpa only [EnvironmentStage.greedyStages, List.length_cons] using congrArg Nat.succ ih
    have hl : (EnvironmentStage.greedyStages (List.ofFn E)).length = H := by simpa using hlen (List.ofFn E)
    simpa only [hl] using DecisionStage.backwardValue_le_length (EnvironmentStage.greedyStages (List.ofFn E)) (initial k)
  have hpolicy : 0 ≤ onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k) := by
    unfold onlineT4SelectedEpisodeValue
    rw [onlineT4SelectedStages_eq_fixed, DecisionStage.trajectoryValue_eq_backwardValue]
    exact DecisionStage.backwardValue_nonneg _ _
  change EnvironmentStage.optimalValue (List.ofFn E) (initial k) -
    onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k) ≤ H
  linarith

theorem mvpActualRegret_sum_le_KH (H K : ℕ) (hH : 0<H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂) ≤ (K : ℝ)*H := by
  calc
    _ ≤ ∑ _k : Fin K, (H : ℝ) := Finset.sum_le_sum (fun k _ =>
      mvpActualEpisodeRegret_le_horizon H K hH E initial fallback path k δ c₁ c₂)
    _ = _ := by simp
end StatisticalRL.OnlineRL
