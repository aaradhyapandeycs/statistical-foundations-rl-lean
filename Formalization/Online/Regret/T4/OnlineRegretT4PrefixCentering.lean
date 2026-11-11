import Formalization.Online.Predictable.OnlinePredictableTestFunction
import Formalization.Online.Regret.T4.OnlineRegretT4Range
import Formalization.Online.Regret.T3.OnlineRegretT3PaddedProcess

/-! T4 true-policy-tail centering on the actual prefix law.
The episode-increment sum identity and Azuma conclusion are separate goals. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t4PrefixStateMeasurable : MeasurableSpace State := ⊤

/-- General predictable-test centering transported to the common path carrier
and its actual reset-vector/prefix sigma-field. -/
theorem onlineSequentialEpisodeLaw_predictableTest_condExp_zero_common
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n m T : ℕ)
    (horizon : T = (m + 1) + n)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner T).rowMeasure
    let f := fun sample => onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m θ
      (horizon ▸ sample)
    μ[f | onlineT3CommonPrefixSigma H K T hH fallback planner n] =ᵐ[μ] 0 := by
  rw [onlineT3CommonPrefixSigma_eq_splitPrefixSigma
    H K T hH E fallback planner (m + 1) n horizon]
  subst T
  simpa only [onlineT3SplitPrefixSigma] using
    onlineSequentialEpisodeLaw_predictableTest_condExp_zero
      H K hH E ρ fallback planner n m θ

/-- True trajectory continuation for the same policy frozen from completed
episodes. It is a function of the revealed prefix, before the next sample. -/
noncomputable def onlineT4PolicyTailAtPrefix
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (planner : OnlineEpisodePlanner State Action H)
    (k : ℕ) (h : Fin H) (history : List (OnlineMDPRow State Action H × State)) : State → ℝ :=
  DecisionStage.trajectoryValue
    ((EnvironmentStage.controlled (List.ofFn E)
      (onlineT4SelectedEpisodePolicy H hH planner history k)).drop (h.val + 1))

end StatisticalRL.OnlineRL
