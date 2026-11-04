import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Source-facing statement draft for onlineRL.tex:1480–1486,
`eq:optimism-Q-V-geq-mvp`. This is not a numbered lemma. It uses the
actual reset/sequential law, the retained-batch causal greedy planner and
the completed-history table. C8 supplies the finite zero-count update; C13
uses the power-of-two trigger from the algorithm's prose; C16 uses the
corrected reciprocal confidence allocation; ties use one fixed maximizing
rule.  -/
namespace StatisticalRL.OnlineRL
open MeasureTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpSourceStatementMeasurable : MeasurableSpace State := ⊤

/-- Both optimal Bellman values are dominated by the actual completed-history
MVP table simultaneously in every episode and stage. -/
def mvpHistoryAllStageOptimism {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δp c₁ c₂ : ℝ) (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ h : Fin H,
    let stages := onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))
    (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) c₁ c₂ stages h.val s) ∧
    (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
      onlineCappedBackwardQAt (H : ℝ) (Real.log (1/δp)) c₁ c₂ stages h.val s a)

/-- Corrected actual-law version of the displayed MVP optimism claim.
The source range is `0 < δ < 1`; strict confidence below implies the
printed weak bound. No event or table-correspondence certificate is assumed. -/
def MVPSourceOptimismCorrected : Prop :=
  ∀ (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ),
    0 < δ → δ < 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1 - 2*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u, 0} State (K*H) | mvpHistoryAllStageOptimism (K := K) hH E fallback δp c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K*H) [] sample.2)}
end StatisticalRL.OnlineRL
