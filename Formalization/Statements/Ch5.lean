import Formalization.Online.QLearning.RateWeightDefinitions
import Formalization.MDP.ActionTrajectoryDefinitions
import Formalization.MDP.PolicyEnvironmentDefinitions
import Formalization.Online.QLearning.ActualRegretDefinitions
import Formalization.Online.QLearning.ActualVisitDefinitions
import Formalization.Online.QLearning.OptimalQDefinitions
import Formalization.Online.Regret.MVP.MVPT5Definitions
import Formalization.Online.Regret.MVP.MVPT2Definitions
import Formalization.Online.Regret.MVP.MVPVarianceDefinitions
import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.MVPUniformSourceDefinitions
import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Mathlib.Probability.Moments.Variance
import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions
import Formalization.Online.Regret.T3.T3Definitions
import Formalization.Online.Regret.PolicyVariance.TrajectoryVarianceDefinitions
import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.Joint.W123Definitions
import Formalization.Online.LowerBound.FamilyDefinitions
import Formalization.Online.LowerBound.BanditDefinitions
import Formalization.Online.LowerBound.RegretDefinitions
import Formalization.Online.Bandit.UCBDefinitions

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


section Lemma53
noncomputable local instance ch5Lemma53StateDecidableEq {State : Type*} : DecidableEq State :=
  Classical.decEq State
noncomputable local instance ch5Lemma53ActionDecidableEq {Action : Type*} : DecidableEq Action :=
  Classical.decEq Action

/-- Lemma 5.3, `lem:sum-inv-Nhk-ucbvi`, `chapters/onlineRL.tex:639–646`.
The deterministic bound holds for every realized finite episode path and every
planner, so the algorithm's actual planner/path are a direct instance. The
first visit is retained by the printed denominator `max{N,1}`. -/
noncomputable def Lemma5_3 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action)
      (initial : Fin K → State) (fallback : State)
      (planner : OnlineEpisodePlanner State Action H)
      (path : OnlineOutcomePath.{u, 0} State (K * H)),
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let history := onlineSequentialPathHistory choose (K * H) [] path
    (∑ k : Fin K, ∑ h : Fin H,
      let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
      (1 : ℝ) / (((max
        ((onlineRowOutcomes (history.take (k.val * H)) (h, rows k.val)).length) 1 : ℕ) : ℝ))) ≤
      2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H *
        (Real.log K / Real.log 2)
end Lemma53

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

/-- Corrected Theorem 5.2, `thm-ucbvi-regret`, `chapters/onlineRL.tex:472–482`,
with source iota at `:726–734` and initial-state law at `:26–33`. The printed
asymptotic bound is strengthened here to the explicit rate below, using the
universal choices c₁=4 and c₂=16. It includes K=1 via the factor 1+iota.
The algorithm uses the finite zero-count completion Q=H and a fixed
deterministic maximizing tie rule; see Candidate C8 in
`docs/SOURCE-ISSUES.md`. The event uses independent identically distributed reset states and the
conditional sequential transition law, together with the true value of the
selected episode policy. -/
noncomputable def Thm5_2_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 0 < K →
    ∀ (E : Fin H → EnvironmentStage State Action)
      (ρ : FiniteDistribution State) (δ : ℝ),
    0 < δ → δ < 1 →
    ∃ c₁ c₂ : ℝ, c₁ = 4 ∧ c₂ = 16 ∧ 0 < c₁ ∧ 0 < c₂ ∧
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let S := Fintype.card State
      let A := Fintype.card Action
      let δ' := δ / (100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
      let I := 40000 * (Real.log K / Real.log 2)^3 *
        Real.log (3 * S * A * H : ℝ) * Real.log (1 / δ')
      let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
      1 - δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
          (∑ k : Fin K,
            (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
              DecisionStage.trajectoryValue
                (EnvironmentStage.controlled (List.ofFn E)
                  (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ')) c₁ c₂))
                (sample.1 k))) ≤
          20 * (Real.sqrt ((S : ℝ) * A * H^3 * K) + (S : ℝ)^2 * A * H^3) * (1 + I)}


/-- Lemma 5.22 (`lemma:sqv`, onlineRL.tex:3612–3615), corrected as described
in `docs/SOURCE-ISSUES.md#C14`: the source coefficient one for centered squares
fails for signed variables, so both bounds use coefficient four. The probability
space is arbitrary and no integrability assumption is added. -/
def Lemma5_22_corrected : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → ∀ C : ℝ, (∀ ω, |X ω| ≤ C) →
      ProbabilityTheory.variance (fun ω => (X ω)^2) μ ≤
          4*C^2 * ProbabilityTheory.variance X μ ∧
      ProbabilityTheory.variance (fun ω => (X ω - ∫ z, X z ∂μ)^2) μ ≤
          4*C^2 * ProbabilityTheory.variance X μ




open StatisticalRL.OnlineRL.MVPProfile

/-- Lemma 5.11 (`lemma:key2`, `chapters/onlineRL.tex:1540–1542`), with
profiles as defined at `:1506–1525`. This stronger row-table form counts profiles
generated by every finite episode-by-stage state-action row table; the source
algorithm's realized profiles form a subset. The printed large-K hypothesis and
final bound are retained. A ceiling comparison family replaces the manuscript's
intermediate family for non-power-of-two K; see `docs/SOURCE-ISSUES.md#C15`.
This is an alternate proof of the printed conclusion, not certification of the
manuscript's intermediate inclusion. -/
noncomputable def Lemma5_11 : Prop :=
  ∀ {State : Type u} {Action : Type v} [Fintype State] [Nonempty State]
    [Fintype Action] [Nonempty Action] (K H : ℕ),
    1 ≤ K → 0 < H →
    (K : ℝ) ≥ (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) *
      (H : ℝ) * logTwoReal K →
    ((sourceMVPFinitePossibleProfiles (K := K) (H := H)
      (Row := State × Action)).card : ℝ) ≤
      (4 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) *
        (H : ℝ) * (K : ℝ)) ^
        ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) *
          (H : ℝ) * logTwoReal K + 1)

/-- Corrected Lemma 5.12 (`lem:sum-inv-Nhk-mvp`,
`chapters/onlineRL.tex:1570–1577`). The trigger is exactly the powers of two,
following the doubling prose at `:1213–1217`; the literal consecutive-integer
trigger set at `:1280` would not satisfy the bound. Arbitrary realized
state/action and successor traces include the corrected algorithm's traces;
stage tags are constructed from the stage clock. The printed pointwise
factor-two comparison also fails, but the displayed final sum bound follows
by dyadic blocks. See `docs/SOURCE-ISSUES.md#C13` for both issues. -/
def Lemma5_12_powerOfTwo_corrected : Prop :=
  ∀ (State Action : Type*) [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (row : ℕ → State × Action) (next : ℕ → State),
    let rowAt : ℕ → Fin H × (State × Action) :=
      fun n => (⟨n % H, Nat.mod_lt n hH⟩, row n)
    (∑ k : Fin K, ∑ h : Fin H,
      (((max ((StatisticalRL.OnlineRL.onlineMVPCountTablesRun rowAt next (k.val * H)).stored
        (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) ≤
      4 * (Fintype.card State : ℝ) * Fintype.card Action * H * (Real.log K / Real.log 2)

/-- Corrected Lemma 5.13 (`lemma:uniform`, `chapters/onlineRL.tex:1696–1712`),
with Assumption X at `:1670–1685`. The confidence allocation is
δ′=δ/(100S²A²H²K²), replacing the printed 100δ/(S²A²H²K²); the printed
generic bound fails under the latter allocation (source issue C16).
The family at current stage h explicitly means the continuation family h+1,
including the terminal endpoint. No generic terminal-zero condition is added.
Families may depend on all strictly-future samples, a stronger class than
the printed empirical-summary dependence. The monotone ceiling cover
includes the printed integer-profile family and all actual profiles (C15).
Level j represents source l=j+2, so every noninitial source level is present;
the K=1 event is vacuous. Both printed inequalities and coefficient 40000
are retained under this corrected allocation. -/
noncomputable def Lemma5_13_confidence_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ), 0 < H → 1 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action),
    (K : ℝ) ≥ (Fintype.card State : ℝ) * Fintype.card Action * H *
      (Real.log K/Real.log 2) →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (family : MVPUniformSource.Profiles (State := State) (Action := Action) H K →
      (h : Fin H) → MVPUniformSource.FutureCode (State := State) (Action := Action) h K →
        Finset (State → ℝ)),
    (∀ p h code, (0 : State → ℝ) ∈ family p h code) →
    (∀ p h code, (family p h code).card ≤ K+1) →
    (∀ p h code V, V ∈ family p h code → ∀ s, 0 ≤ V s ∧ V s ≤ H) →
    let S : ℝ := Fintype.card State
    let A : ℝ := Fintype.card Action
    let δ' := δ/(100*S^2*A^2*(H:ℝ)^2*(K:ℝ)^2)
    let I := 40000*(Real.log K/Real.log 2)^3*Real.log (3*S*A*H)*Real.log (1/δ')
    1-δ' ≤ (FiniteHorizonGenerative.samplingLaw E K).real {data |
      ∀ p : MVPUniformSource.Profiles (State := State) (Action := Action) H K,
      ∀ j : Fin (Nat.log2 K), ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (MVPUniformSource.futureData h K data)) →
      let Z := fun (h : Fin H) (s : State) (a : Action) =>
        (MVPUniformSource.batchRow data j h s a).expectation (X h s a) -
          ((E h).transition s a).expectation (X h s a)
      (∑ h : Fin H, ∑ s : State, ∑ a : Action, Z h s a) ≤
        (∑ h : Fin H, ∑ s : State, ∑ a : Action, max (Z h s a) 0) ∧
      (∑ h : Fin H, ∑ s : State, ∑ a : Action, max (Z h s a) 0) ≤
        Real.sqrt ((S*A*H*I/(2^(j.val+2)*(Real.log K/Real.log 2))) *
          ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (X h s a)) +
          S*A*(H:ℝ)^2*I/(2^(j.val+2)*(Real.log K/Real.log 2))}

/-- Corrected MVP optimism, `eq:optimism-Q-V-geq-mvp`,
`chapters/onlineRL.tex:1480–1487`. The actual law has iid
resets and conditionally sampled transitions, and uses a fixed deterministic
greedy tie rule. C8 gives the finite zero-count update, C13 uses the prose
power-of-two trigger, and C16 replaces the printed allocation 100δ/(S²A²H²K²) by
δ/(100S²A²H²K²). See `docs/SOURCE-ISSUES.md`. The standing regime K≥SAH·Iota at
`chapters/onlineRL.tex:1402–1407` is retained in this indexed statement. -/
noncomputable def MVP_optimism_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ),
    0 < δ → δ < 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    (Fintype.card State : ℝ)*Fintype.card Action*H*I ≤ (K : ℝ) →
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1 - 2*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u, 0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          ∀ k : Fin K, ∀ h : Fin H,
            let stages := onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))
            (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
              onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) c₁ c₂ stages h.val s) ∧
            (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
              onlineCappedBackwardQAt (H : ℝ) (Real.log (1/δp)) c₁ c₂ stages h.val s a)}


/-! Private source-facing snippet. Definition-only imports should include
MVPModelDefinitions, W1Definitions and the existing sequential definitions. -/

/-- Corrected Lemma 5.15, `lem:bound-T6-ucb-mvp`,
`source/upstream/tex/chapters/onlineRL.tex:1822–1833`. The actual MVP
sequential law uses iid episode resets and conditional transition sampling.
T2 uses the source bonus for positive counts and the C8 analysis charge H
for zero counts. C13 reads the trigger as a power of two,
and C16 uses the corrected reciprocal confidence allocation; one deterministic
greedy tie rule is fixed. The K=1 case is included by a direct argument.
See `docs/SOURCE-ISSUES.md`. -/
noncomputable def Lemma5_15_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1 - 4*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          let U := fun (h : Fin H) (k : Fin K) =>
            onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) c₁ c₂
              (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) (h.val+1)
          let sa := fun (h : Fin H) (k : Fin K) =>
            onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val
          let stage := fun (h : Fin H) (k : Fin K) =>
            let hist := history.take (k.val*H)
            letI : Nonempty State := (E h).state_nonempty
            onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
              (onlineMVPHistoryNextAt fallback hist) hist.length h
          (∑ h : Fin H, ∑ k : Fin K, ((E h).transition (sa h k).1 (sa h k).2).variance (U h k)) ≤
            4*(H : ℝ)*(∑ h : Fin H, ∑ k : Fin K,
              if hp : 0 < ((stage h k).observations (sa h k).1 (sa h k).2).length then
                c₁ * Real.sqrt ((onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k) *
                  Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length) +
                c₂*(H : ℝ)*Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length
              else H) +
            4*(H : ℝ)*(∑ h : Fin H, ∑ k : Fin K,
              max ((onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).expectation (U h k) -
                ((E h).transition (sa h k).1 (sa h k).2).expectation (U h k)) 0) +
            (K : ℝ)*(H : ℝ)^2*I}


/-- Corrected displayed MVP T2 bound `eq:T2-ub-analysis-mvp`,
`source/upstream/tex/chapters/onlineRL.tex:1793–1801`. The source's suitably
chosen coefficients are fixed to (4,16), and K≥2. The actual retained-table
history uses the C8 zero-count analysis charge H and positive-count source
bonus, C13 power-of-two trigger, C16 reciprocal confidence allocation, and
one fixed deterministic greedy tie rule. This is a displayed estimate, not a
separate numbered lemma. The standing regime K≥SAH·Iota at
`chapters/onlineRL.tex:1402–1407` is retained in this indexed statement. -/
noncomputable def MVP_T2_K2_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H)) (δ : ℝ),
    0 < δ → δ ≤ 1 →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    (Fintype.card State : ℝ)*Fintype.card Action*H*I ≤ (K : ℝ) →
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) 4 16
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
    let U := fun (h : Fin H) (k : Fin K) =>
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) 4 16
        (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) (h.val+1)
    let sa := fun (h : Fin H) (k : Fin K) =>
      onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let stage := fun (h : Fin H) (k : Fin K) =>
      let hist := history.take (k.val*H)
      letI : Nonempty State := (E h).state_nonempty
      onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
        (onlineMVPHistoryNextAt fallback hist) hist.length h
    (∑ h : Fin H, ∑ k : Fin K,
      if 0 < ((stage h k).observations (sa h k).1 (sa h k).2).length then
        4 * Real.sqrt ((onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k) *
          Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length) +
        16*(H : ℝ)*Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length
      else H) ≤
      (1/2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H *
        (∑ h : Fin H, ∑ k : Fin K,
          (onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k)) * I) +
      (1/2 : ℝ) * (Fintype.card State : ℝ) * Fintype.card Action * (H : ℝ)^2 * I


/-- Corrected displayed MVP T5 bound `eq:T5-ub-analysis-mvp`,
`source/upstream/tex/chapters/onlineRL.tex:1804–1810`. The actual retained-table
sequential law uses iid resets and conditional transition sampling; K≥1,
including the direct K=1 case. Coefficients are fixed to (4,16), with the C8
zero-count analysis charge H, C13 power-of-two trigger, C16 reciprocal confidence
allocation, and one deterministic greedy tie rule. This displayed estimate is
not a separate numbered lemma. The standing regime K≥SAH·Iota at
`chapters/onlineRL.tex:1402–1407` is retained in this indexed statement. -/
noncomputable def MVP_T5_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ), 0 < δ → δ ≤ 1 →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    (Fintype.card State : ℝ)*Fintype.card Action*H*I ≤ (K : ℝ) →
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) 4 16
    1 - 2 * Real.log (K*H) * δp ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          let U := fun (h : Fin H) (k : Fin K) =>
            onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) 4 16
              (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) (h.val+1)
          let sa := fun (h : Fin H) (k : Fin K) =>
            onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val
          let stage := fun (h : Fin H) (k : Fin K) =>
            let hist := history.take (k.val*H)
            letI : Nonempty State := (E h).state_nonempty
            onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
              (onlineMVPHistoryNextAt fallback hist) hist.length h
          (∑ h : Fin H, ∑ k : Fin K,
            (onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k)) ≤
          (∑ h : Fin H, ∑ k : Fin K,
            ((onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).expectation (fun s => (U h k s)^2) -
              ((E h).transition (sa h k).1 (sa h k).2).expectation (fun s => (U h k s)^2))) +
          2*(H : ℝ)*(∑ h : Fin H, ∑ k : Fin K,
            if 0 < ((stage h k).observations (sa h k).1 (sa h k).2).length then
              4 * Real.sqrt ((onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k) *
                Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length) +
              16*(H : ℝ)*Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length
            else H) +
          Real.sqrt ((H : ℝ)^2 * (∑ h : Fin H, ∑ k : Fin K,
            ((E h).transition (sa h k).1 (sa h k).2).variance (U h k)) * I) +
          (K : ℝ)*(H : ℝ)^2*I}

/-- Corrected joint displayed MVP T2/T3/T4 estimates,
`eq:T2-ub-analysis-mvp`, `eq:T3-ub-analysis-mvp`,
`eq:T4-ub-analysis-mvp`, `source/upstream/tex/chapters/onlineRL.tex:1793–1802`.
The actual retained-table planner uses the universal coefficients (4,16),
the C8 zero-count analysis charge H, the C13 power-of-two trigger, the
C16 reciprocal confidence allocation, and one fixed maximizing tie.
K≥2 is explicit for this auxiliary logarithmic event (C12).
The three inequalities hold on one event under the same sequential law.
The standing large-K regime at lines 1402–1407 is retained below; C16
also changes the confidence-dependent Iota in that condition.
This is a displayed estimate, not a separate numbered source lemma.
-/
noncomputable def MVP_T234_K2_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (fallback : State) (δ : ℝ), 0 < δ → δ ≤ 1 →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    (Fintype.card State : ℝ)*Fintype.card Action*H*I ≤ (K : ℝ) →
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) 4 16
    1 - 4*(Real.log K/Real.log 2)*δp ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          let U := fun (h : Fin H) (k : Fin K) =>
            onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) 4 16
              (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) (h.val+1)
          let sa := fun (h : Fin H) (k : Fin K) =>
            onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val
          let stage := fun (h : Fin H) (k : Fin K) =>
            let hist := history.take (k.val*H)
            letI : Nonempty State := (E h).state_nonempty
            onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
              (onlineMVPHistoryNextAt fallback hist) hist.length h
          let next := fun (h : Fin H) (k : Fin K) =>
            (history.map Prod.snd).getD (k.val*H+h.val) fallback
          let T5 := ∑ h : Fin H, ∑ k : Fin K,
            (onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k)
          let T6 := ∑ h : Fin H, ∑ k : Fin K,
            ((E h).transition (sa h k).1 (sa h k).2).variance (U h k)
          ((∑ h : Fin H, ∑ k : Fin K,
            if 0 < ((stage h k).observations (sa h k).1 (sa h k).2).length then
              4 * Real.sqrt ((onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).variance (U h k) *
                Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length) +
              16*(H : ℝ)*Real.log (1/δp) / ((stage h k).observations (sa h k).1 (sa h k).2).length
            else H) ≤
            (1/2 : ℝ)*Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*T5*I) +
              (1/2 : ℝ)*(Fintype.card State : ℝ)*Fintype.card Action*(H : ℝ)^2*I) ∧
          (|∑ h : Fin H, ∑ k : Fin K,
            (((E h).transition (sa h k).1 (sa h k).2).expectation (U h k) -
              U h k (next h k))| ≤ Real.sqrt (T6*I)+(H : ℝ)*I) ∧
          (|∑ k : Fin K,
            ((∑ h : Fin H, (E h).reward (sa h k).1 (sa h k).2) -
              DecisionStage.trajectoryValue
                (List.ofFn (fun h : Fin H => (E h).withPolicy
                  (fun s => EnvironmentStage.pointMass (planner (history.take (k.val*H)) h s))))
                (sample.1 k))| ≤ Real.sqrt ((K : ℝ)*(H : ℝ)^2*I))}



universe uMvpRegret vMvpRegret

/-- Corrected explicit form of the MVP regret theorem, `thm-mvp-regret`,
`chapters/onlineRL.tex:1339–1352`. The source soft-O rate is made explicit
with a universal constant and the source polylogarithmic factor `max 1 I`.
This includes K=1 directly, where the printed proof factor I vanishes (C12).
Universal bonus witnesses are c₁=4,c₂=16; one fixed maximizing tie is used.
The algorithm uses the finite zero-count completion (C8), power-of-two
triggers (C13), and reciprocal confidence δp (C16), replacing the printed
numerator-100 allocation. The ceiling profile cover and terminal-zero
auxiliary family repair the proof gaps C15/C17. These disclosed corrections
and source-scope notes are recorded in `docs/SOURCE-ISSUES.md`. The true value
of the same completed-history deployed policy defines each regret term. -/
noncomputable def MVP_regret_corrected : Prop :=
  ∃ C : ℝ, 0<C ∧
    ∀ (State : Type uMvpRegret) (Action : Type vMvpRegret)
      [Fintype State] [Fintype Action] (H K : ℕ) (hH : 0<H),
      0<K → ∀ (E : Fin H → EnvironmentStage State Action)
        (ρ : FiniteDistribution State) (δ : ℝ),
      0<δ → δ<1 →
      ∃ c₁ c₂ : ℝ, c₁=4 ∧ c₂=16 ∧ 0<c₁ ∧ 0<c₂ ∧
        let fallback : State := Classical.choice (E ⟨0,hH⟩).state_nonempty
        let S := Fintype.card State
        let A := Fintype.card Action
        let δp := δ/(100*(S:ℝ)^2*(A:ℝ)^2*(H:ℝ)^2*(K:ℝ)^2)
        let I := 40000*(Real.log K/Real.log 2)^3*
          Real.log (3*(S:ℝ)*A*H)*Real.log (1/δp)
        let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
        1-δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
          {sample : (Fin K → State) × OnlineOutcomePath.{uMvpRegret,0} State (K*H) |
            let history := onlineSequentialPathHistory
              (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
            (∑ k : Fin K,
              (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
                DecisionStage.trajectoryValue
                  (List.ofFn (fun h : Fin H => (E h).withPolicy
                    (fun s => EnvironmentStage.pointMass (planner (history.take (k.val*H)) h s))))
                  (sample.1 k))) ≤
              C*max 1 I*min (Real.sqrt ((S:ℝ)*A*(H:ℝ)^3*K)) ((H:ℝ)*K)}

/-- Corrected Lemma 5.14, `lemma:decouple`,
`source/upstream/tex/chapters/onlineRL.tex:1722–1744`. The event is stated on
the actual sequential experiment with iid episode resets and conditional
transition sampling, and uses the retained empirical row, completed
pre-episode history, and fixed maximizing tie. It includes the K=1 endpoint.
The zero-count rule (C8), trigger convention (C13), confidence allocation
(C16), profile cover (C15), and terminal-zero family (C17) are documented
corrections or proof-scope repairs in `docs/SOURCE-ISSUES.md`. -/
noncomputable def Lemma5_14_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    (Fintype.card State : ℝ)*Fintype.card Action*H*
      (Real.log K/Real.log 2) ≤ (K : ℝ) →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1 - δp <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          let U := fun (h : Fin H) (k : Fin K) =>
            onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) c₁ c₂
              (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) (h.val+1)
          let sa := fun (h : Fin H) (k : Fin K) =>
            onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val
          let stage := fun (h : Fin H) (k : Fin K) =>
            let hist := history.take (k.val*H)
            letI : Nonempty State := (E h).state_nonempty
            onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
              (onlineMVPHistoryNextAt fallback hist) hist.length h
          let err := fun (h : Fin H) (k : Fin K) =>
            (onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).expectation (U h k) -
              ((E h).transition (sa h k).1 (sa h k).2).expectation (U h k)
          let errSq := fun (h : Fin H) (k : Fin K) =>
            (onlineObservedPlanningRow (stage h k) (sa h k).1 (sa h k).2).expectation
                (fun s => (U h k s)^2) -
              ((E h).transition (sa h k).1 (sa h k).2).expectation (fun s => (U h k s)^2)
          let T6 := ∑ h : Fin H, ∑ k : Fin K,
            ((E h).transition (sa h k).1 (sa h k).2).variance (U h k)
          let d := (Fintype.card State : ℝ)*Fintype.card Action*H
          ((∑ h : Fin H, ∑ k : Fin K, err h k) ≤
            (∑ h : Fin H, ∑ k : Fin K, max (err h k) 0)) ∧
          ((∑ h : Fin H, ∑ k : Fin K, max (err h k) 0) ≤
            Real.sqrt (d*I*T6)+d*(H : ℝ)*I) ∧
          ((∑ h : Fin H, ∑ k : Fin K, errSq h k) ≤
            Real.sqrt (d*(H : ℝ)^2*I*T6)+d*(H : ℝ)^2*I)}

noncomputable local instance ch5Claim51StateDecidableEq {State : Type*} : DecidableEq State :=
  Classical.decEq State
noncomputable local instance ch5Claim51ActionDecidableEq {Action : Type*} : DecidableEq Action :=
  Classical.decEq Action

/-- Corrected Claim 5.1, `claim:PV-l-UB`,
`source/upstream/tex/chapters/onlineRL.tex:4340–4353` (proved in the book at
`:4406–4476`, inside the proof of Lemma 5.14). Stated on the actual sequential
experiment (iid episode resets, conditional transition sampling) for the MVP
learner with completed pre-episode history, with the premises of
`Lemma5_14_corrected` (`4 ≤ c₁`, `c₁² ≤ c₂`, the source standing premise
`SAH·log₂K ≤ K`). Differences from the printed claim, recorded in
`docs/SOURCE-ISSUES.md` (C8, C13, C15, C16 and its Claim 5.1 note, C17):
(i) the confidence allocation is the reciprocal `δ′ = δ/(100S²A²H²K²)` with
`δ ≤ 1` instead of the printed `100δ/(S²A²H²K²)`; the claim at the printed
allocation is neither proved nor refuted here (C16 refutes only the generic
Lemma 5.13 allocation); (ii) the claim is restricted to one fixed committed
maximizing tie rule; (iii) the algorithm uses the zero-count completion (C8)
and power-of-two triggers (C13), and the proof uses the profile cover and
terminal-zero auxiliary family repairs (C15, C17); (iv) the printed proof
applies Lemma 5.13 at level `l = 1` (`:4464`), which that lemma does not cover;
the formal proof treats `l = 1` deterministically (each term ≤ `H`, total
`≤ dH ≤ dHI/(2 log₂K)`). Reading conventions (not corrections): the sum over
`(s,a,h)` at episode `k_{l,j,s,a,h}` is written over stages `h` and zero-based
episodes `k` whose stage-`h` pair has exactly `2^(l-1)+j-1` earlier visits
(each pair has at most one such episode; a pair with no such visit contributes
`0`, the source's `V^k = 0` for `k > K`); `V^k_{h+1}` is the capped backward
value `U h k` built from the history before episode `k`; `P̂^{(l)}_{s,a,h}` is
the empirical row of the successors of `(h,s,a)` at its zero-based visits
`2^(l-2),…,2^(l-1)-1` (`l ≥ 2`) or its first visit (`l = 1`), read from the
completed history (the `fallback` default is never read at an actual visit);
`log₂K = log K / log 2` and `l` ranges over naturals `1 ≤ l ≤ log₂K`. The event
holds with probability strictly exceeding `1 − δ′`. -/
noncomputable def Claim5_1_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    (Fintype.card State : ℝ)*Fintype.card Action*H*
      (Real.log K/Real.log 2) ≤ (K : ℝ) →
    let δp := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) * Real.log (1/δp)
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1 - δp <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          let U := fun (h : Fin H) (k : Fin K) =>
            onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δp)) c₁ c₂
              (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))) (h.val+1)
          let sa := fun (h : Fin H) (e : ℕ) =>
            onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h e
          let cnt := fun (h : Fin H) (k : Fin K) =>
            ((Finset.range k.val).filter (fun e => sa h e = sa h k.val)).card
          let Phat := fun (l : ℕ) (h : Fin H) (k : Fin K) =>
            FiniteDistribution.empiricalRow (2^(l-2)) (by positivity)
              (fun q : Fin (2^(l-2)) => (onlineRowOutcomes history (h, sa h k.val)).getD
                ((if l = 1 then 0 else 2^(l-2)) + q.val) fallback)
          let d := (Fintype.card State : ℝ)*Fintype.card Action*H
          let x := Real.log K / Real.log 2
          ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ x → ∀ j : ℕ, 1 ≤ j → j ≤ 2^(l-1) →
            (∑ h : Fin H, ∑ k : Fin K,
              if cnt h k = 2^(l-1)+j-1 then
                (Phat l h k).expectation (U h k) -
                  ((E h).transition (sa h k.val).1 (sa h k.val).2).expectation (U h k)
              else 0) ≤
            Real.sqrt (d*I/(2^l*x) * ∑ h : Fin H, ∑ k : Fin K,
                if cnt h k = 2^(l-1)+j-1 then
                  ((E h).transition (sa h k.val).1 (sa h k.val).2).variance (U h k)
                else 0) +
              d*(H : ℝ)*I/(2^l*x)}


local instance qLearningIndexStateMeasurable (State : Type*) : MeasurableSpace State := ⊤
local instance qLearningIndexPathMeasurable (State : Type u) (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State n) := ⊤

/-- Source Lemma 5.18 (`lemma:opt_model_free`, onlineRL.tex:2121–2150), for
the explicitly completed Q-learning algorithm: a fixed deterministic greedy tie
selector and initial nonterminal `V=min(H,max Q)=H`. The universal source
bonus coefficient is witnessed by `c_b=2`, and the residual constant by `8`.
The probability is under the actual iid-reset, sequential-transition law;
all episode indices below are zero-based. The algorithm completion and tie
restriction are recorded in `docs/SOURCE-ISSUES.md`, C20. -/
noncomputable def Lemma5_18_restricted : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ),
    0 < δ → δ < 1 →
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let beta := fun t : ℕ => if t=0 then 0 else 4*(2:ℝ)*Real.sqrt ((H:ℝ)^3*L/(t:ℝ))
    1-δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
        (beta 0 = 0 ∧ ∀ t : ℕ, 0<t → beta t ≤ 4*(2:ℝ)*Real.sqrt ((H:ℝ)^3*L/(t:ℝ))) ∧
        (∀ (k : Fin K) (r : OnlineMDPRow State Action H),
          let visits := qLearningActualVisitEpisodes hH E bonus sample.1 fallback sample.2 k r
          let t := visits.length
          let hist := qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2
          let gap := ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
            (qLearningChronologicalValue hH E
              (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 ((visits.get i)*H))
              (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
             qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback))
          0 ≤ (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)).q r - qLearningTrueOptimalQ E r ∧
          (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
            onlineQRateWeight H t 0 * (H:ℝ) + gap +
              beta t) ∧
        (∀ (k : Fin K) (h : Fin H) (s : State),
          EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
            qLearningChronologicalValue hH E
              (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)) h.val s)}

/-- Source Theorem 5.16 (`thm-ucbq-regret`, onlineRL.tex:1911–1922),
for the fixed deterministic greedy tie selector and initial nonterminal V=H
completion. The original bonus uses cb=2 and log(SAT/δ); the explicit soft-O
rate uses Λ=1+log(4SAT/δ) and universal constant max(1,19e). The proof
uses the corrected shifted-beta inequality and retains signed stage weights.
See `docs/SOURCE-ISSUES.md`, C20, for the algorithm completion, tie
restriction and proof repairs; no literal printed-proof-validity claim is made. -/
noncomputable def Thm5_16_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => 2*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let Λ := 1+Real.log (4*((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ))/δ)
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    1-δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
      qLearningActualRegret hH E bonus sample.1 fallback sample.2 ≤
        max 1 (19*Real.exp 1)*Real.sqrt ((H:ℝ)^5*(Fintype.card (State×Action):ℝ)*(K:ℝ)*Λ)}

/-- Lemma 5.17, `lemma:property_lr`, `chapters/onlineRL.tex:2020–2041`, for the
learning rates `η_n = (H+1)/(H+n)` of `eq:learning_rate_ucbq` (`chapters/onlineRL.tex:1898–1904`).
`onlineQRateWeight H N n` is the source weight `η_n^N`. For every horizon `H ≥ 1` and
`N ≥ 1`: the two `1/√n`-weighted bounds and the square bound; and for every `n ≥ 1` the
tail series `∑_{N ≥ n} η_n^N` converges to `1 + 1/H` (re-indexed as `N = n + k`). -/
def Lemma5_17 : Prop :=
  ∀ (H : ℕ), 0 < H →
    (∀ (N : ℕ), 0 < N →
      1 / Real.sqrt (N : ℝ) ≤
          (∑ n ∈ Finset.Icc 1 N, onlineQRateWeight H N n / Real.sqrt (n : ℝ)) ∧
        (∑ n ∈ Finset.Icc 1 N, onlineQRateWeight H N n / Real.sqrt (n : ℝ)) ≤
          2 / Real.sqrt (N : ℝ) ∧
        (∑ n ∈ Finset.Icc 1 N, (onlineQRateWeight H N n) ^ 2) ≤ 2 * (H : ℝ) / (N : ℝ)) ∧
    (∀ (n : ℕ), 0 < n →
      HasSum (fun k : ℕ => onlineQRateWeight H (n + k) n) (1 + 1 / (H : ℝ)))

open StatisticalRL.OnlineLowerBound in
/-- `lem:Vh-star-Vhpi-gap-lower-bound-online-final`, `chapters/onlineRL.tex:2654–2668` (Lemma 5.20).
For every MDP `M_i` of the two-state family `C^sub_mdp` and every nonstationary randomized Markov
policy `π`, `V⋆_1(1) − V^π_1(1) ≥ ∑_{h=1}^H ε₀(H−h)/(16H²)(1 − π_h(a⋆_h | 1))`.
Encodings: the source's 1-based step `h` is `(h : Fin H) + 1`; the source's arms `1, …, A` are
`Fin A` with arm `1` the index `0` (`onlineLBq` follows the printed case split of
`eqn:prob-astar-a-1`); the absorbing state `0` has the action set `Fin A` with all actions identical,
which meets the source's singleton action set there; `0 < ε ≤ H/2` is the construction's standing
range (`:2602`), passed as arguments of `onlineLBSubStages`. Values are the project's
backward-induction optimal value and actual trajectory value. -/
def Lemma5_20 : Prop :=
  ∀ (H A : ℕ) (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2)
    (i : Fin H → Fin A) (π : ℕ → StationaryPolicy (Fin 2) (Fin A)),
    ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) *
        (1 - (π h 1).prob (i h)) ≤
      EnvironmentStage.optimalValue (List.ofFn (onlineLBSubStages H ε hH hε hεH i)) 1 -
        DecisionStage.trajectoryValue
          (EnvironmentStage.controlled (List.ofFn (onlineLBSubStages H ε hH hε hεH i)) π) 1

open StatisticalRL.OnlineLowerBound in
/-- `lem:online-lb-testing`, `chapters/onlineRL.tex:2709–2721` (Lemma 5.21). For `A ≥ 3`, `H ≥ 2`,
`0 < ε₀ ≤ H/2` and every round `t ≤ H³A/(18ε₀²)`, every online bandit algorithm satisfies
`(1/A) ∑_i P_{B_i}(a_{t+1} ≠ i) ≥ 1/3` (the infimum over algorithms is written as `∀ L`).
Encodings: arm `1` is the index `0`; rewards are `Bool` with `P_i(R = true | a) = 1 − q_i(a)`;
`banditNextArmErrorProb` draws the history of the first `t` rounds from the adaptive interaction law
of `B_i` and the next arm from the learner's rule at round index `t`. `BanditLearner` allows an
internal random seed with a finite law (a seed-free learner is a one-point seed), so the class is at
least as large as the printed one. The printed proof's unlabelled KL chain rule is
`AdaptiveKL.interactionLaw_klDiv`; see `docs/SOURCE-ISSUES.md` for the recorded proof-level notes. -/
def Lemma5_21 : Prop :=
  ∀ (A H : ℕ), 3 ≤ A → ∀ (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε) (hεH : ε ≤ (H : ℝ) / 2) (t : ℕ),
    (t : ℝ) ≤ (H : ℝ) ^ 3 * A / (18 * ε ^ 2) →
    ∀ L : BanditLearner A,
      (1 : ℝ) / 3 ≤ (1 / (A : ℝ)) * ∑ i : Fin A, banditNextArmErrorProb L H ε hH hε hεH i t

open StatisticalRL.OnlineLowerBound in
/-- `thm:minimax-lower-online`, `chapters/onlineRL.tex:2443–2456` (Theorem 5.19). There is a universal
`c₀ > 0` such that for all `S ≥ 2`, `A ≥ 3`, `H ≥ 2`, `K ≥ 1` some finite family of horizon-`H`
nonstationary MDPs on `Fin S` with actions `Fin A`, and an initial law `ρ`, force every online learner
to expected regret `E[∑_{k=1}^K (V⋆_1(ρ) − V^{π^k}_1(ρ))] ≥ c₀ min{√(H³SAK), HK}` on some member (the
`inf sup` over the finite family is written as `∀ L, ∃ i`).
Encodings: exactly `A` actions per state meets "at most `A` actions per state"; `OnlineLearner`
selects before episode `k` a nonstationary randomized Markov policy from the previous episodes and an
internal random seed with a finite law (a seed-free learner is a one-point seed), at least as strong as
printed; episode records `(s₁, (a_h, s_{h+1})_{h<H})` include the final state and omit rewards, which
the learner can recompute since rewards are state-determined for the hard family; each episode starts
at `s₁ ∼ ρ` independently of the past. The library proof (witness `c₀ = 1/1536`) uses the general-`S`
family with odd `S` padded by an unreachable absorbing state and a direct adaptive-KL argument in place
of the printed induced-algorithm reduction and binomial case analysis; these proof-level gaps of the
printed argument are recorded in `docs/SOURCE-ISSUES.md` (C25–C27). -/
def Thm5_19 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (S A H K : ℕ), 2 ≤ S → 3 ≤ A → 2 ≤ H → 1 ≤ K →
    ∃ (I : Type) (_ : Fintype I) (E : I → Fin H → EnvironmentStage (Fin S) (Fin A))
      (ρ : FiniteDistribution (Fin S)),
      ∀ L : OnlineLearner (Fin S) (Fin A) H, ∃ i : I,
        c₀ * min (Real.sqrt ((H : ℝ) ^ 3 * S * A * K)) ((H : ℝ) * K) ≤
          onlineExpectedRegret (E i) ρ L K

open StatisticalRL.Bandit in
/-- Restricted `thm:bandit-pure-ucb` (Theorem 5.1), `chapters/bandits.tex:258–277`; model
`:9–83`, Algorithm 5.1 `:207–251`, proof `:387–501`.

For `A` arms with mean rewards `r a ∈ [0,1]`, horizon `T` with `2 ≤ A ≤ T`, and `0 < δ < 1`, let
`L = log(T²/δ)`, `r⋆ = max_a r a` (written `⨆ a, r a`) and `Δ(a) = r⋆ - r a`. The noise table
`z : Fin T → Fin A → ℝ` (`z t a` is the noise of arm `a` at round `t`) has independent `N(0,1)`
entries (`:37–42`). UCB (Algorithm 5.1) pulls at each round an arm of maximal index
`r^sum(a)/N(a) + √(2L/N(a))`, the index being `+∞` when `N(a) = 0` (the convention of `:387`).
Rounds are 0-indexed. The pseudo-regret `T r⋆ - Σ_t r(a_t)` (`:67–72`) is integrable, and its
expectation over the noise satisfies (5.1a) `≤ 8 √(A T L)` and (5.1b)
`≤ 10 L Σ_{a : Δ(a) > 0} 1/Δ(a)`.

Restricted variant: the printed algorithm leaves the choice inside the argmax unspecified
(`:232`). This entry covers every deterministic rule `tie t s ∈ s` that depends only on the round
and the argmax set. It does not cover history-dependent or randomized tie-breaking. Both printed
bounds and constants, and all printed hypotheses, are unchanged. See
`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures` for the scope and
`docs/SOURCE-ISSUES.md#C36` for the repair of the printed proof's Step 1. -/
def Thm5_1_restricted : Prop :=
  ∀ (A T : ℕ) (r : Fin A → ℝ) (δ : ℝ) (tie : ℕ → Finset (Fin A) → Fin A),
    (∀ t s, s.Nonempty → tie t s ∈ s) → 2 ≤ A → A ≤ T →
    (∀ a, r a ∈ Set.Icc (0 : ℝ) 1) → 0 < δ → δ < 1 →
    let L := Real.log ((T : ℝ) ^ 2 / δ)
    let rstar := ⨆ a, r a
    let Δ := fun a => rstar - r a
    let regret := fun z : Fin T → Fin A → ℝ => (T : ℝ) * rstar - ∑ t, r (ucbAction tie L r z t)
    Integrable regret (gaussianNoiseTable T A) ∧
    ∫ z, regret z ∂gaussianNoiseTable T A ≤ 8 * Real.sqrt (A * T * L) ∧
    ∫ z, regret z ∂gaussianNoiseTable T A
      ≤ 10 * L * ∑ a ∈ Finset.univ.filter (fun a => 0 < Δ a), 1 / Δ a

open StatisticalRL.Bandit StatisticalRL.GaussianBanditLB in
/-- Remark 5.12 (`chapters/onlineRL.tex:2725–2729`, unlabeled; numbered by the per-chapter remark
counter), lower-bound part. This is the formal reading of an informal remark: the argument of
Lemma 5.21 (`lem:online-lb-testing`, `:2709–2721`), with the Bernoulli KL replaced by the Gaussian
one, gives a minimax lower bound of order `√(AT)` for the Gaussian bandit of `sec:bandits-UCB`
(`chapters/bandits.tex:15–48`; pseudo-regret `:66–70`), matching Theorem 5.1 up to logarithmic
factors (`:296`). The remark gives no constant; `1/16` is ours.

For `2 ≤ A ≤ T` there is a family of `A` mean vectors `μ i ∈ [0,1]^A`, fixed before the learner,
such that every learner incurs expected pseudo-regret at least `(1/16)√(AT)` on some member.
A learner is a seed `σ` from an arbitrary probability space `(Seed, ν)`, independent of the noise,
and arm maps `arm t σ h` of the seed and the history `h : Fin t → Fin A × ℝ` of past (arm, reward)
pairs. Requirement disclosed: each `(σ, h) ↦ arm t σ h` is measurable (`Fin A` carries the
discrete σ-algebra); this is needed for the expected regret to be defined. Every randomized
history-dependent algorithm with measurable rules is of this form, and UCB with a deterministic
tie rule is the case `Seed = Unit`. The noise table has independent `N(0,1)` entries
(`:37–42`), and the regret is shown integrable, so the integral is not a junk value. This is the
fixed-family (inf–sup over learners after the family) form, which implies the `∀ L ∃ μ` form.
Disclosure: the seed space is quantified as `Seed : Type` (universe 0); this covers every seed space
used in practice, e.g. `ℕ → unitInterval` for per-round uniforms. -/
def Remark5_12_lowerBound : Prop :=
  ∀ (A T : ℕ), 2 ≤ A → A ≤ T →
    ∃ μ : Fin A → Fin A → ℝ, (∀ i a, μ i a ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A),
        (∀ t, Measurable (Function.uncurry (arm t))) →
        ∃ i : Fin A,
          Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => regret arm (μ i) T ω.1 ω.2)
            (ν.prod (gaussianNoiseTable T A)) ∧
          (1 / 16 : ℝ) * Real.sqrt ((A : ℝ) * T) ≤
            ∫ ω, regret arm (μ i) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A))

open StatisticalRL.Bandit StatisticalRL.GaussianBanditLB in
/-- Restricted Remark 5.12 (`chapters/onlineRL.tex:2725–2729`): minimax optimality of UCB up to
logarithmic factors (the notion of `chapters/bandits.tex:296`) for the Gaussian bandit of
`sec:bandits-UCB`. Formal reading of an informal remark.

For `2 ≤ A ≤ T`, `0 < δ < 1` and `L = log(T²/δ)`: there is a family of mean vectors in `[0,1]^A`
such that for every learner (as in `Remark5_12_lowerBound`: a seed from an arbitrary probability
space plus arm maps `arm t` measurable in `(σ, h)`) some member `μ i` satisfies both
`(1/16)√(AT) ≤ E_{μ i}[Regret_L]` and, for every mean vector `r ∈ [0,1]^A`, the expected
pseudo-regret of UCB (Algorithm 5.1, `:207–251`) on `r` is integrable and at most
`128 √L · E_{μ i}[Regret_L]`. Since this holds for every learner, UCB's worst-case regret over
`[0,1]^A` is within the factor `128√L` of the minimax value over `[0,1]^A` (the best worst-case
regret of any learner). The seed space is quantified as `Seed : Type` (universe 0), as in
`Remark5_12_lowerBound`.

Restricted variant: the UCB part inherits the tie-rule restriction of `Thm5_1_restricted`. It
covers every deterministic tie rule `tie t s ∈ s` depending only on the round and the argmax set.
See `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`. -/
def Remark5_12_restricted : Prop :=
  ∀ (A T : ℕ) (δ : ℝ) (tie : ℕ → Finset (Fin A) → Fin A),
    (∀ t s, s.Nonempty → tie t s ∈ s) → 2 ≤ A → A ≤ T → 0 < δ → δ < 1 →
    let L := Real.log ((T : ℝ) ^ 2 / δ)
    ∃ μ : Fin A → Fin A → ℝ, (∀ i a, μ i a ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A),
        (∀ t, Measurable (Function.uncurry (arm t))) →
        ∃ i : Fin A,
          Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => regret arm (μ i) T ω.1 ω.2)
            (ν.prod (gaussianNoiseTable T A)) ∧
          (1 / 16 : ℝ) * Real.sqrt ((A : ℝ) * T) ≤
            ∫ ω, regret arm (μ i) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A)) ∧
          ∀ r : Fin A → ℝ, (∀ a, r a ∈ Set.Icc (0 : ℝ) 1) →
            Integrable (fun z : Fin T → Fin A → ℝ =>
                (T : ℝ) * (⨆ a, r a) - ∑ t, r (ucbAction tie L r z t))
              (gaussianNoiseTable T A) ∧
            ∫ z, ((T : ℝ) * (⨆ a, r a) - ∑ t, r (ucbAction tie L r z t))
                ∂gaussianNoiseTable T A ≤
              128 * Real.sqrt L *
                ∫ ω, regret arm (μ i) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A))

/-- Corrected regret-to-PAC conversion, `eq:PAC-from-regret-conversion` (`-regret`, `-pac`) with
`eq:uniform-policy-pihat`, `chapters/onlineRL.tex:113–141`; protocol `chapters/onlineRL.tex:17–41`.
Differs from the printed result in the constant: `C`, the regret constant at the actual
`(S, A, H)`, replaces the printed `C_{S,A,H+1}`, which is false (regret-to-PAC entry in
`docs/SOURCE-ISSUES.md`; refutation `RegretToPAC.not_Eq_PAC_from_regret_conversion_printed`).
The regret hypothesis is assumed only at the given instance `(H, K, E, ρ)`, which is weaker than
the printed "for any MDP with S states, A actions and horizon H". Algorithm class (restricted):
finitely supported internal randomness (`ν` on a finite `Seed`) and deployed policies that are
deterministic Markov given the seed and the completed history; the source also allows
randomized deployed policies (:35–38), which are not covered. `π̂ = π^J` with `J` uniform and
independent; the joint (seed, run, J) probability is written as the seed- and J-average.
`0 < H`, `0 < K`, `0 < δ`; `α ∈ [0,1]` as printed. The printed proof (:145–183) runs the
algorithm on an augmented MDP; this entry is proved directly (the episode-k start state is
independent of `πᵏ`). -/
def Eq_PAC_from_regret_conversion_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (Seed : Type) [Fintype Seed] (H K : ℕ) (hH : 0 < H), 0 < K →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (fallback : State) (ν : FiniteDistribution Seed)
      (planner : Seed → OnlineEpisodePlanner State Action H) (C α δ : ℝ),
    0 ≤ α → α ≤ 1 → 0 < δ →
    let law : Seed →
        FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
      fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
    let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
        Fin K → Fin H → State → Action :=
      fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
          (k.val * H))
    let V : (Fin H → State → Action) → State → ℝ := fun f ↦
      DecisionStage.trajectoryValue
        (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
    let Vstar : State → ℝ :=
      DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
    ν.expectation (fun ω ↦ (law ω).expectation (fun sample ↦
        ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) ≤
      C * (K : ℝ) ^ (1 - α) →
    1 - δ ≤ ν.expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
      (law ω).rowMeasure.real {sample |
        ρ.expectation Vstar - ρ.expectation (V (πk ω sample k)) ≤ C * (K : ℝ) ^ (-α) / δ})

/-- Restricted regret-to-PAC conversion with the printed constant `C_{S,A,H+1}`,
`eq:PAC-from-regret-conversion`, `chapters/onlineRL.tex:113–141`; protocol
`chapters/onlineRL.tex:17–41`. The printed statement with one added premise: the regret constant
is nondecreasing in the horizon at the instance's `(S, A)`, `C_{S,A,H} ≤ C_{S,A,H+1}` (without it
the printed statement is false; regret-to-PAC entry in `docs/SOURCE-ISSUES.md`). The algorithm
(seed law `ν H K`, planner `alg H K r ω`) sees the horizon, `K`, the known reward table and its
seed, not the transitions or `ρ`; the regret hypothesis is over every MDP on the given carriers
with `0 < H`, `0 < K`. Same restricted algorithm class as
`Eq_PAC_from_regret_conversion_corrected`. -/
def Eq_PAC_from_regret_conversion_restricted : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (Seed : Type) [Fintype Seed] (ν : ℕ → ℕ → FiniteDistribution Seed)
    (alg : (H : ℕ) → ℕ → (Fin H → State → Action → ℝ) → Seed →
      OnlineEpisodePlanner State Action H)
    (C : ℕ → ℕ → ℕ → ℝ) (α : ℝ), 0 ≤ α → α ≤ 1 →
    (∀ H : ℕ, C (Fintype.card State) (Fintype.card Action) H ≤
      C (Fintype.card State) (Fintype.card Action) (H + 1)) →
    (∀ (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State),
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      (ν H K).expectation (fun ω ↦ (law ω).expectation (fun sample ↦
          ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) ≤
        C (Fintype.card State) (Fintype.card Action) H * (K : ℝ) ^ (1 - α)) →
    ∀ (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State) (δ : ℝ),
      0 < δ →
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      1 - δ ≤ (ν H K).expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
        (law ω).rowMeasure.real {sample |
          ρ.expectation Vstar - ρ.expectation (V (πk ω sample k)) ≤
            C (Fintype.card State) (Fintype.card Action) (H + 1) * (K : ℝ) ^ (-α) / δ})

end StatisticalRL.Statements
