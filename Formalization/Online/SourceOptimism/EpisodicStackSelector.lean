import Formalization.Online.SourceOptimism.StackRunCylinderIdentity
import Formalization.Online.SourceOptimism.FreshCoordinateSelection
import Formalization.MDP.FiniteOptimal
import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions

/-! Causal episodic selector and actual
stage-specific successor streams; trajectory-law equality is not established in this module. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineEpisodicStateMeasurable : MeasurableSpace State := ⊤
noncomputable def onlineMDPStackLaw {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K : ℕ) :
    Measure (OnlineMDPRow State Action H × Fin K → State) :=
  onlineStackProductLaw (fun i => onlineMDPSuccessorRowLaw E i.1)

/-- Source iid episode resets are independent of the successor stacks. -/
noncomputable def onlineMDPInitialStackLaw {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State) (K : ℕ) :
    Measure ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)) :=
  (Measure.pi (fun _ : Fin K => ρ.rowMeasure)).prod (onlineMDPStackLaw E K)

/-- The chronological stage tag is fixed by source episode/stage indexing. -/
theorem onlineEpisodicChoose_stage (H K : ℕ) (hH : 0<H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State)) :
    (onlineEpisodicChoose H K hH initial fallback planner history).1.val=history.length%H := rfl

/-- At episode start the actual state is exactly the supplied reset coordinate. -/
theorem onlineEpisodicCurrentState_reset (H K : ℕ) (hH : 0<H)
    (initial : Fin K → State) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (hlen : history.length=k.val*H) :
    onlineEpisodicCurrentState H K initial fallback history=initial k := by
  have hdiv : k.val * H / H = k.val := by
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left k.val hH
  simp [onlineEpisodicCurrentState, hlen, hdiv, k.isLt]

end StatisticalRL.OnlineRL
