import Formalization.Online.Regret.Definitions
import Formalization.Online.SourceOptimism.GreedySequentialTrajectoryOptimism
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Definitions for the restricted K≥2 corrected-zero-count W₁ statement.
The fixed deterministic tie rule and actual sequential-history law are retained.
This file contains no theorem or proof declarations. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance W1DefinitionsStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance W1DefinitionsActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualStageRowSequence
    (H K : ℕ) (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (h : Fin H) : ℕ → State × Action :=
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  let rowAt := onlineTranscriptRowSequence (choose []) history
  fun e => (rowAt (e * H + h.val)).2

noncomputable def onlineActualPolicyContinuation
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : State → ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  DecisionStage.trajectoryValue ((EnvironmentStage.controlled (List.ofFn E)
    (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂)).drop (h.val + 1))

noncomputable def onlineActualOptimisticContinuation
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : State → ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
    (onlinePreEpisodePlanningStages E history k.val) (h.val + 1)

noncomputable def onlineActualT6Policy
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    ((E h).transition sa.1 sa.2).variance
      (onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k)

noncomputable def onlineActualT6Difference
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)

noncomputable def onlineW1SourceIota (S A H K : ℕ) (δ' : ℝ) : ℝ :=
  40000 * (Real.log K / Real.log 2)^3 * Real.log (3 * S * A * H : ℝ) * Real.log (1 / δ')

noncomputable def onlineActualW1RestrictedIotaEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ' c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ'
    (∑ k : Fin K, onlineActualEpisodeW1 H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
      (1 / 8 : ℝ) * Real.sqrt (S * A * H *
        onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
      (1 / 8 : ℝ) * Real.sqrt (S * A * H *
        onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
      (1 / 8 : ℝ) * S * A * H^2 * I}
end StatisticalRL.OnlineRL
