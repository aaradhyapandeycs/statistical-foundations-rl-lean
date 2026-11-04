import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.Joint.W123Definitions

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

/-- W₁ clause of `lem:bound-W1-W2-ucbvi-proof`,
`chapters/onlineRL.tex:928–953`, with W₁ defined at lines 910–922 and iota
at lines 726–733. This entry proves only the W₁ inequality, with the printed
confidence and coefficients; the other two clauses are indexed separately below.
It restricts the episode count to K ≥ 2 because the printed logarithmic
factor vanishes at K = 1 (Candidate C12 in `docs/SOURCE-ISSUES.md`). It also
uses the explicit finite zero-count convention Q = H (Candidate C8), the
source domain 0 < δ ≤ 1, and one fixed deterministic greedy tie rule.
The T₆ policy variance and squared difference are evaluated along the same
actual path, against the true transition row and the same selected policy.
No concentration event or variance estimate is assumed. -/
noncomputable def Lemma5_7_W1_K2_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action)
      (ρ : FiniteDistribution State) (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let δ' := δ / (100 * S^2 * A^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let iota := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * Fintype.card State * Fintype.card Action * H : ℝ) * Real.log (1 / δ')
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 12 * S^2 * A * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{0, 0} State (K * H) |
          (∑ k : Fin K, onlineActualEpisodeW1 H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
            (1 / 8 : ℝ) * Real.sqrt (S * A * H *
              onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * Real.sqrt (S * A * H *
              onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * S * A * H^2 * iota}

/-- Complete corrected/restricted `lem:bound-W1-W2-ucbvi-proof`,
`chapters/onlineRL.tex:925–957`. W₁ and W₂ are defined at lines 910–922,
W₃ at line 931, the joint confidence at line 935, and the three bounds at
lines 938–946. Iota is the printed quantity at lines 726–733.
This states all three inequalities on ONE event for the actual reset-vector
and causal sequential-path law. The same played rows, pre-episode empirical
rows, selected true-policy continuations and optimistic continuations define
the W and T₆ quantities; no concentration or variance estimate is assumed.
The episode restriction K≥2 addresses the vanishing-log endpoint (Candidate
C12 in `docs/SOURCE-ISSUES.md`). The algorithm uses the finite zero-count
convention Q=H (Candidate C8), one fixed deterministic greedy tie rule,
and the source confidence/bonus domains. Singleton state spaces are included.
The original unrestricted K=1 source lemma is not certified by this entry. -/
noncomputable def Lemma5_7_K2_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action)
      (ρ : FiniteDistribution State) (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let δ' := δ / (100 * S^2 * A^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let iota := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * Fintype.card State * Fintype.card Action * H : ℝ) * Real.log (1 / δ')
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 12 * S^2 * A * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{0, 0} State (K * H) |
          ((∑ k : Fin K, onlineActualEpisodeW1 H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
            (1 / 8 : ℝ) * Real.sqrt (S * A * H *
              onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * Real.sqrt (S * A * H *
              onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * S * A * H^2 * iota) ∧
          ((∑ k : Fin K, onlineActualEpisodeW2 H K hH E sample.1 fallback sample.2 k δ' c₁ c₂) ≤
            (1 / 8 : ℝ) * Real.sqrt (S^2 * A * H *
              onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * S^2 * A * H^2 * iota) ∧
          ((∑ h : Fin H, ∑ k : Fin K,
              onlineActualW3Point H K hH E sample.1 fallback sample.2 δ' c₁ c₂ h k) ≤
            (1 / 8 : ℝ) * Real.sqrt (S * A * H^3 *
              onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * Real.sqrt (S^2 * A * H^3 *
              onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * iota) +
            (1 / 8 : ℝ) * S^2 * A * H^3 * iota)}

end StatisticalRL.Statements
