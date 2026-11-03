import Formalization.Online.SourceOptimism.StackRunCylinderIdentity
import Formalization.Online.SourceOptimism.FreshCoordinateSelection
import Formalization.MDP.FiniteOptimal

/-! Causal episodic selector and actual
stage-specific successor streams; trajectory-law equality is not established in this module. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineEpisodicStateMeasurable : MeasurableSpace State := ⊤
abbrev OnlineMDPRow (State Action : Type*) (H : ℕ) := Fin H × (State × Action)

/-- The planner sees only completed episodes and chooses a policy table.
Its later action depends on the within-episode history only via current state. -/
abbrev OnlineEpisodePlanner (State Action : Type*) (H : ℕ) :=
  List (OnlineMDPRow State Action H × State) → Fin H → State → Action

/-- Episode starts use the independent initial-state coordinate. Other stages
use the preceding actual successor. Fallback totalizes impossible/out-of-budget
histories; bounded actual runs never use it for an episode start. -/
def onlineEpisodicCurrentState (H K : ℕ) (initial : Fin K → State)
    (fallback : State) (history : List (OnlineMDPRow State Action H × State)) : State :=
  if history.length%H=0 then
    if hk : history.length/H<K then initial ⟨history.length/H,hk⟩ else fallback
  else ((history.getLast?).map Prod.snd).getD fallback

/-- Source episode k chooses its policy from episodes strictly before k.
The state resets at every stage-zero boundary; the terminal successor is stored
but does not become the following episode's initial state. -/
def onlineEpisodicChoose (H K : ℕ) (hH : 0<H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State)) : OnlineMDPRow State Action H :=
  let h : Fin H := ⟨history.length%H,Nat.mod_lt _ hH⟩
  let s := onlineEpisodicCurrentState H K initial fallback history
  (h,(s,planner (history.take ((history.length/H)*H)) h s))

/-- Row law is the actual nonstationary MDP successor distribution. -/
def onlineMDPSuccessorRowLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (r : OnlineMDPRow State Action H) : FiniteDistribution State :=
  (E r.1).transition r.2.1 r.2.2

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
