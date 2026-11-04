import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.Regret.Definitions

/-! Corrected source-facing Chapter 5 statement index. -/
open scoped BigOperators
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

universe u v

/-- Corrected `lemma:decomdetail`, `chapters/onlineRL.tex:808–818`.
The pre-episode observed tables and realized state/action path are arbitrary;
the selected action is required to maximize the same backward Q table, as in
the algorithm's greedy rule. Thus this statement covers every greedy tie
choice. The domain `0 < δ' ≤ 1`, `c₁,c₂ ≥ 0` includes the source's positive
bonus constants and confidence allocation. The sole semantic correction is
the finite analysis charge H at zero visits, where the printed bonus divides
by zero; positive counts use the printed Bernstein formula. See Candidate C8
in `docs/SOURCE-ISSUES.md`. No optimism or probability event is assumed. -/
noncomputable def Lemma5_6_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    [Nonempty State] [Nonempty Action] (H : ℕ), 0 < H →
    ∀ (stage : Fin H → OnlineObservedPlanningStage State Action)
      (state : ℕ → State) (action : ℕ → Action) (δ' c₁ c₂ : ℝ),
    0 < δ' → δ' ≤ 1 → 0 ≤ c₁ → 0 ≤ c₂ →
    (∀ h : Fin H,
      onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val))) →
    onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
        (List.ofFn stage) (state 0) ≤
      ∑ n ∈ Finset.range H,
        if hn : n < H then
          let h : Fin H := ⟨n, hn⟩
          let tail := onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
            ((List.ofFn stage).drop (n + 1))
          (stage h).environment.reward (state n) (action n) +
            onlineRegretAnalysisCharge (H : ℝ) (Real.log (1 / δ')) c₁ c₂
              (stage h) tail (state n) (action n) +
            ((onlineObservedPlanningRow (stage h) (state n) (action n)).expectation tail -
              ((stage h).environment.transition (state n) (action n)).expectation tail) +
            (((stage h).environment.transition (state n) (action n)).expectation tail -
              tail (state (n + 1)))
        else 0

end StatisticalRL.Statements
