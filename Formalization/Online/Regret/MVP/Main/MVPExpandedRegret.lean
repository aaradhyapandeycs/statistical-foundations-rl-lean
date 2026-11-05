import Formalization.Online.Regret.MVP.Main.MVPActualRegret

/-! source-expression bridge; no probability claim. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualEpisodeRegret_eq_expanded
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (δp c₁ c₂ : ℝ) :
    mvpActualEpisodeRegret H K hH E initial fallback path k δp c₁ c₂ =
      DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (initial k) -
      DecisionStage.trajectoryValue
        (List.ofFn (fun h : Fin H => (E h).withPolicy (fun s => EnvironmentStage.pointMass
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
            ((mvpVarianceHistory H K hH E initial fallback path δp c₁ c₂).take (k.val*H)) h s))))
        (initial k) := by
  unfold mvpActualEpisodeRegret onlineT4SelectedEpisodeValue
  dsimp only
  rw [← EnvironmentStage.greedy_trajectoryValue, onlineT4SelectedStages_eq_fixed]
  rfl
end StatisticalRL.OnlineRL
