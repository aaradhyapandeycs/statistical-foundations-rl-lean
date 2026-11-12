import Formalization.Online.Regret.T3.OnlineRegretT3FiberIntegral
import Formalization.Online.SourceOptimism.SequentialTranscriptUniqueness

/-!
# Full joint-law T₃ prefix-fiber sum

finite-sum consumer. It identifies a fiber of the actual map
(initial reset vector, reconstructed n-record history) with all suffixes of a
fixed initial/prefix pair, then applies the already proved continuation sum.
This is still a finite set-integral precursor, not a conditional-expectation
claim.
-/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance onlineT3PrefixStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineT3PrefixActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action

/-- History visible at time `n` in a full path, using the actual episode
planner selected by that sample's reset vector. -/
noncomputable def onlineT3PrefixHistory
    (H K : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (initial : Fin K → State) (n m : ℕ)
    (path : OnlineOutcomePath.{uState, 0} State (m + n)) :
      List (OnlineMDPRow State Action H × State) :=
  @onlineSequentialPathHistory (OnlineMDPRow State Action H) State
    (onlineEpisodicChoose H K hH initial fallback planner) n []
    (show OnlineOutcomePath.{uState, 0} State n from
      @onlineSequentialPathPrefix.{uState, 0, 0} State n m path)

end StatisticalRL.OnlineRL
