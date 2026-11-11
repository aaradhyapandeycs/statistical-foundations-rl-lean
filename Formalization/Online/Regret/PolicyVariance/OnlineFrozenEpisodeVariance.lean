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

end StatisticalRL.OnlineRL
