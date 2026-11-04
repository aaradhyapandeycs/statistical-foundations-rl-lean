import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions

/-! Corrected source-facing Chapter 5 statement index. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.Statements
open StatisticalRL.OnlineRL
local instance stateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Corrected `lemma:opt`, `chapters/onlineRL.tex:765–775`. The algorithm uses the
explicit zero-count convention Q = H and one fixed deterministic maximizing
tie rule; this statement restricts the confidence parameter to 0 < δ ≤ 1.
See `docs/SOURCE-ISSUES.md` Candidate C8 for the zero-count gap and
Candidate C6 for the separate confidence-factor discrepancy in the printed proof. -/
noncomputable def Lemma5_5_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 0 < K →
    ∀ (E : Fin H → EnvironmentStage State Action)
      (ρ : FiniteDistribution State) (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
    let δ' := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{0, 0} State (K * H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
          ∀ k : Fin K, ∀ h : Fin H,
            (∀ s, DecisionStage.trajectoryValue
              ((EnvironmentStage.greedyStages (List.ofFn E)).drop h.val) s ≤
              onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ')) c₁ c₂
                (onlinePreEpisodePlanningStages E history k.val) h.val s) ∧
            (∀ s a, DecisionStage.trajectoryQ
              ((EnvironmentStage.greedyStages (List.ofFn E)).drop h.val) s a ≤
              onlineCappedBackwardQAt (H : ℝ) (Real.log (1 / δ')) c₁ c₂
                (onlinePreEpisodePlanningStages E history k.val) h.val s a)}
end StatisticalRL.Statements
