import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.W1.W1Definitions

/-! Actual-law variance and gap proof component: actual stage policy gap definition.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

noncomputable def onlineActualStagePolicyGap
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let U := onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂
    (onlinePreEpisodePlanningStages E history k.val) h.val sa.1
  let P := DecisionStage.trajectoryValue
    ((EnvironmentStage.controlled (List.ofFn E)
      (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂)).drop h.val) sa.1
  U - P

end StatisticalRL.OnlineRL
