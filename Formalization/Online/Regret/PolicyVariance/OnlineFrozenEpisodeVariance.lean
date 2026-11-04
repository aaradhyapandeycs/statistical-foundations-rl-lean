import Formalization.Online.Regret.PolicyVariance.FiniteTrajectoryVarianceHorizon
import Formalization.Online.Regret.Definitions

/-! Actual-law variance and gap proof component: OnlineFrozenEpisodeVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance frozenVarianceStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance frozenVarianceActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineControlledStages_length
    (es : List (EnvironmentStage State Action)) (π : ℕ → StationaryPolicy State Action) :
    (EnvironmentStage.controlled es π).length = es.length := by
  induction es generalizing π with
  | nil => rfl
  | cons e es ih => simp [EnvironmentStage.controlled, ih]

/-- For any specified pre-episode history and initial state, the selected
frozen policy's static controlled-trajectory law has expected cumulative
successor-value transition variance at most H². -/
theorem onlineFrozenEpisode_expected_variance_le_horizon_sq
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (initial : State) (L c₁ c₂ : ℝ) :
    let π := onlineCappedEpisodePolicy H hH E history k L c₁ c₂
    let stages := EnvironmentStage.controlled (List.ofFn E) π
    (DecisionStage.trajectoryLaw stages initial).expectation (finiteTrajectoryVarianceSum stages initial) ≤
      (H : ℝ)^2 := by
  let π := onlineCappedEpisodePolicy H hH E history k L c₁ c₂
  let stages := EnvironmentStage.controlled (List.ofFn E) π
  have hh := finiteTrajectory_expected_variance_le_horizon_sq stages initial
  have hlen : stages.length = H := by simp [stages, onlineControlledStages_length]
  simpa [hlen] using hh
end StatisticalRL.OnlineRL
