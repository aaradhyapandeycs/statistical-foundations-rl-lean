import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions
import Formalization.Online.Regret.T3.T3Definitions
import Formalization.Online.Regret.PolicyVariance.TrajectoryVarianceDefinitions
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


/-- Lemma 5.4, `lem:cum-var-ub-Hsquare-ucbvi-mean`,
`chapters/onlineRL.tex:648–658`. A deterministic stage-dependent policy is
executed in the true MDP. The expectation averages its actual trajectory law
from each initial state under an arbitrary initial distribution. The recursive
variance sum adds each true transition-row variance of the same policy's
remaining trajectory value; its terminal continuation is zero. -/
noncomputable def Lemma5_4 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H : ℕ), 0 < H →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (π : Fin H → State → Action),
    let stages := List.ofFn (fun h => (E h).withPolicy
      (fun s => EnvironmentStage.pointMass (π h s)))
    ρ.expectation (fun s =>
      (DecisionStage.trajectoryLaw stages s).expectation
        (finiteTrajectoryVarianceSum stages s)) ≤ (H : ℝ)^2


/-- Corrected/restricted Lemma 5.8, `lem:bound-T234`,
`chapters/onlineRL.tex:988–1005`. All four displayed inequalities (including
both parts of the T3 radius chain) hold on one actual sequential experiment.
The printed iota and its lower-bound hypothesis are retained. The algorithm
uses the finite zero-count completion and one fixed deterministic maximizing
tie rule; K ≥ 2 is explicit. Candidate C8 in `docs/SOURCE-ISSUES.md` records the
zero-count correction, and C12 records the missing endpoint: at K=H=1 the
printed strict probability bound would require probability > 1.
The full unrestricted printed lemma and the final regret theorem are not
asserted by this entry. -/
noncomputable def Lemma5_8_K2_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
    let δ' := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) *
        Real.log (1 / δ')
    8 * max (c₁^2) c₂ * (Real.log K / Real.log 2) * Real.log (1 / δ') ≤ I →
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 4 * (Real.log ((K : ℝ) * H) / Real.log 2) * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) |
          (∑ k : Fin K,
            (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.1) ≤
            (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H *
              onlineActualT5 H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
              (1 / 2 : ℝ) * (Fintype.card State : ℝ) * Fintype.card Action * H^2 * I ∧
          |∑ k : Fin K,
            (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.1| ≤
            Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ∧
          Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
            Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ≤
            4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) +
            4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ∧
          |∑ k : Fin K,
            (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.2| ≤
            Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ'))}

/-- Corrected/restricted Lemma 5.9, `lem:bound-T56`,
`chapters/onlineRL.tex:1055–1092`. The first event contains all three
displayed T5/T6 bounds with the printed 14-confidence coefficient. Under
the printed large-K condition, the second event contains both simplified
bounds with the printed 30-confidence coefficient. All quantities refer
to the same reset-vector and actual causal sequential experiment.
The universal bonus constants are chosen as c₁=4 and c₂=16, independently
of all problem and confidence parameters. T0 is written out using its
source definition at lines 1027–1033; iota is the printed quantity at
lines 726–734. No concentration or variance estimate is a hypothesis.
The implementation uses the finite zero-count completion and H analysis
charge (Candidate C8 in `docs/SOURCE-ISSUES.md`) and one fixed deterministic
maximizing tie rule. K≥2 is explicit for the auxiliary logarithmic proof
route (Candidate C12); the unrestricted K=1 claim is not certified here. -/
noncomputable def Lemma5_9_K2_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (δ : ℝ), 0 < δ → δ < 1 →
    let fallback : State := Classical.choice (E ⟨0,hH⟩).state_nonempty
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let δ' := δ / (100*S^2*A^2*(H:ℝ)^2*(K:ℝ)^2)
    let L := Real.log (1/δ')
    let I := 40000*(Real.log K/Real.log 2)^3*Real.log (3*S*A*H)*L
    let planner := onlineCappedGreedyPlanner E L 4 16
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    let T0 := fun sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) =>
      (3/8:ℝ)*Real.sqrt (S*A*H*
        onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' 4 16*I) +
      (3/8:ℝ)*Real.sqrt (S^2*A*H*
        onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' 4 16*I) +
      (1/4:ℝ)*S^2*A*H^2*I + 7*Real.sqrt ((K:ℝ)*(H:ℝ)^2)*L +
      onlineActualT2 H K hH E sample.1 fallback sample.2 δ' 4 16
    (1-14*S^2*A*H^2*K*δ' ≤
      μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
        onlineActualT5 H K hH E sample.1 fallback sample.2 δ' 4 16 ≤
          (∑ h : Fin H, ∑ k : Fin K,
            onlineActualW3Point H K hH E sample.1 fallback sample.2 δ' 4 16 h k) +
          2*(H:ℝ)*onlineActualT2 H K hH E sample.1 fallback sample.2 δ' 4 16 +
          2*(K:ℝ)*(H:ℝ)^2 +
          Real.sqrt (32*(H:ℝ)^2*onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' 4 16*L) +
          5*(H:ℝ)^2*L ∧
        onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' 4 16 ≤
          (K:ℝ)*(H:ℝ)^2+Real.sqrt (2*((K:ℝ)*(H:ℝ)^6)*L) ∧
        onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' 4 16 ≤
          2*(H:ℝ)^2*T0 sample+18*(H:ℝ)^2*L}) ∧
    (S*A*H^2*I ≤ (K:ℝ) →
      1-30*S^2*A*H^2*K*δ' ≤
        μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
          onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' 4 16 ≤
            2*(K:ℝ)*(H:ℝ)^2 ∧
          onlineActualT5 H K hH E sample.1 fallback sample.2 δ' 4 16 ≤
            6*(K:ℝ)*(H:ℝ)^2 +
            (1/2:ℝ)*Real.sqrt (S^2*A*H^3*
              onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' 4 16*I) +
            4*S^2*A*H^3*I})


end StatisticalRL.Statements
