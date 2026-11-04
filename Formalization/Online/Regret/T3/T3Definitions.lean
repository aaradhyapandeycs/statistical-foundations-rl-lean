import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.Definitions

/-! Definition-only source-facing T₃ data definitions. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3DefinitionsEventStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t3DefinitionsEventStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3DefinitionsEventActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The source's optimistic-continuation variance sum on the actual path. -/
noncomputable def onlineActualT6UCB
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    ((E h).transition sa.1 sa.2).variance
      (onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k)

/-- The source's actual T₃ inequality event, with the public decomposition
coordinate and the printed T₆-policy/T₆-difference expansion. -/
@[irreducible] def onlineActualT3SourceBoundEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ' c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample |
    |∑ k : Fin K,
      (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.1|
      ≤ Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2
          δ' c₁ c₂ * Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ∧
    Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2
        δ' c₁ c₂ * Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ')
      ≤ 4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2
          δ' c₁ c₂ * Real.log (1 / δ')) +
        4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2
          δ' c₁ c₂ * Real.log (1 / δ')) +
        5 * (H : ℝ) * Real.log (1 / δ')}


end StatisticalRL.OnlineRL
