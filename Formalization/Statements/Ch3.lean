import Formalization.Statements.Ch3Definitions
import Formalization.Generative.GenerativeLowerBoundTwoStateDefinitions
import Formalization.Probability.VarianceDefinitions

/-! # Chapter 3 statement index

Each entry below gives the complete statement in the source-facing objects.
Proof applications are kept in `Ch3Proofs.lean`. -/

open MeasureTheory ProbabilityTheory
open StatisticalRL.DiscountedMDP

namespace StatisticalRL.Statements.Ch3

local instance statementFinMeasurable (S : ℕ) : MeasurableSpace (Fin S) := ⊤
local instance statementStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Source `thm:model-based-policy-eval`,
`source/upstream/tex/chapters/generative_model_model_based.tex:140–156`.
The universal constant is chosen before the finite cardinalities, model,
policy, accuracy, confidence and sample count. The witness `hN` is explicit
because the Lean empirical-frequency model is defined for positive sample
counts; the source threshold itself forces `N > 0` on its stated range. -/
def Thm3_1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (S A N : ℕ)
    (M : DiscountedMDP (Fin S) (Fin A))
    (π : StationaryPolicy (Fin S) (Fin A)) (δ ε : ℝ),
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    c * Real.log (S / (δ * (1 - M.discount))) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
    ∃ hN : 0 < N,
      1 - δ ≤ (StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M π N).real
        {data | ‖StatisticalRL.ModelBasedPolicyEvaluation.valueEstimator M π N hN data -
          M.trajectoryExpectedValue π‖ ≤ ε}

/-- Restricted positive-sample version of source `Thm:sample-compl-main`,
`source/upstream/tex/chapters/generative_model_model_based.tex:900–923`.
This entry makes the existing empirical-frequency export's `N > 0`
restriction explicit. See
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). -/
def Thm3_2_positiveN : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ ε : ℝ),
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    c₀ * Real.log
      (Fintype.card State * Fintype.card Action * N /
        ((1 - M.discount) ^ 2 * ε * δ)) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
    1 - δ ≤
      (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ f : State → Action,
          StatisticalRL.ModelBasedPolicyLearning.EmpiricallyOptimal M N hN data f →
            (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
              M.trajectoryExpectedValue
                (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
            (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
                M.discount * ε ≤
              M.trajectoryExpectedQ
                (fun t ↦ EnvironmentStage.pointMass (f t)) s a)}

/-- Source `LemAbsToNormalV`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1254–1263`.
The absorbing model uses the original model's actual optimal trajectory value
at `x` as its replacement reward parameter. -/
def Lemma3_3 : Prop :=
  ∀ (State Action : Type*) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (x s : State),
    StatisticalRL.ModelBasedPolicyLearning.optimalTrajectoryValue
      (StatisticalRL.ModelBasedPolicyLearning.optimalValueAbsorbingModel M x) s =
      StatisticalRL.ModelBasedPolicyLearning.optimalTrajectoryValue M s

/-- Source `LemValueCover`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1292–1300`.
For the same positive-size empirical data, a grid point covers the actual
optimal trajectory-value function within one grid step. -/
def Lemma3_4 : Prop :=
  ∀ (State Action : Type*) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : StatisticalRL.ModelBasedPolicyLearning.Samples State Action N)
    (x : State),
    ∃ i : Fin (N + 1),
      ‖StatisticalRL.ModelBasedPolicyLearning.valueEstimator M N hN data -
        StatisticalRL.ModelBasedPolicyLearning.absorbingGridValue
          (StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data)
          N hN x i‖ ≤
        StatisticalRL.ModelBasedPolicyLearning.absorbingGridStep M N hN

/-- Restricted positive-sample version of source `lem:policy-learning-evaluation`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1306–1326`.
It retains the source's simultaneous norm and pointwise one-sided conclusions.
The positive sample-count restriction is explicit for the empirical-frequency
model; see [`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). -/
def Lemma3_5_positiveN : Prop :=
  ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ : ℝ),
    0 < δ → δ < 1 →
    c₀ * StatisticalRL.ModelBasedPolicyLearning.leaveOneOutBeta M N δ /
      (1 - M.discount) ≤ N →
    1 - δ ≤
      (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ f : State → Action,
          StatisticalRL.ModelBasedPolicyLearning.EmpiricallyOptimal M N hN data f →
            ‖(StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).trajectoryExpectedValue
                (fun t ↦ EnvironmentStage.pointMass (f t)) -
              M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
              c₁ * Real.sqrt
                (2 * StatisticalRL.ModelBasedPolicyLearning.leaveOneOutBeta M N δ /
                  (N * (1 - M.discount) ^ 3)) ∧
            ∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
                M.trajectoryExpectedValue
                  (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
              M.trajectoryExpectedValue M.optimalGreedyPolicy s -
                M.trajectoryExpectedValue
                  (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤
                2 * c₁ * Real.sqrt
                  (StatisticalRL.ModelBasedPolicyLearning.leaveOneOutBeta M N δ /
                    (N * (1 - M.discount) ^ 3))}

/-- Causal-planner, positive-sample restriction of source `Thm:sample-compl-finite`,
`source/upstream/tex/chapters/generative_model_model_based.tex:2551–2570`.
The source does not fix an optimal-policy tie choice; this proved variant uses
the concrete deterministic backward-greedy selector with its fixed fallback
rule. It also states `N > 0` explicitly for the empirical-frequency model.
See [`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures).
The assumptions `0 < ε ≤ H` imply `H > 0`, which supplies a deterministic
fallback action from the first environment stage. -/
def Thm3_9_causal_positiveN : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (H : ℕ) (hH : 0 < H)
      (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεH : ε ≤ H),
    c₀ * (H : ℝ) ^ 3 *
      Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) /
        ε ^ 2 ≤ N →
    1 - δ ≤
      (StatisticalRL.FiniteHorizonGenerative.samplingLaw E N).real
        {data |
          let fallback : Action := Classical.choice ((E ⟨0, hH⟩).action_nonempty)
          let f := StatisticalRL.FiniteHorizonGenerative.backwardGreedyActions fallback
            (StatisticalRL.FiniteHorizonGenerative.empiricalStages E N hN data)
          ∀ h : Fin H,
            (∀ s,
              EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s -
                StatisticalRL.FiniteHorizonGenerative.policyTrajectorySuffix (List.ofFn E) f
                  h.val s ≤ ε) ∧
            (∀ s a,
              EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a -
                StatisticalRL.FiniteHorizonGenerative.policyTrajectoryQSuffix (List.ofFn E) f
                  h.val s a ≤ ε)}

noncomputable local instance statementStateDecidable (State : Type*) : DecidableEq State :=
  Classical.decEq State

open scoped Matrix in
/-- Lemma 3.6, `lem:empirical-value-residual`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1395–1410`, on the event
`eq:Bernstein-empirical-optimal-value` (lines 1373–1376). `π̂⋆` is any deterministic policy
`f` that is optimal for the empirical model `P̂` built from `N > 0` samples per state-action pair
(the source does not fix a tie rule), `V̂⋆` is the empirical optimal value
(`valueEstimator`), `P_{π̂⋆}` is written out as the matrix `(s,t) ↦ (P_{π̂⋆}(s))(t)` and
`(I - γ P_{π̂⋆})⁻¹` is its true resolvent. The confidence parameter `β₁` only needs
`β₁ ≥ 0` here (the source has `β₁ ≥ 4`). -/
def Lemma3_6 : Prop :=
  ∀ (State Action : Type*) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : StatisticalRL.ModelBasedPolicyLearning.Samples State Action N)
    (f : State → Action) (β : ℝ), 0 ≤ β →
    StatisticalRL.ModelBasedPolicyLearning.EmpiricallyOptimal M N hN data f →
    let H := StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data
    let π : StationaryPolicy State Action := fun t ↦ EnvironmentStage.pointMass (f t)
    let Vs := StatisticalRL.ModelBasedPolicyLearning.valueEstimator M N hN data
    (∀ s, |(H.policyTransition π s).expectation Vs - (M.policyTransition π s).expectation Vs| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.policyTransition π s).variance Vs) +
        2 * β / (N * (1 - M.discount))) →
    M.discount * ‖(1 - M.discount • (Matrix.of fun s t ↦ (M.policyTransition π s).prob t))⁻¹ *ᵥ
      (fun s ↦ |(H.policyTransition π s).expectation Vs -
        (M.policyTransition π s).expectation Vs|)‖ ≤
      2 * Real.sqrt (2 * β / (N * (1 - M.discount) ^ 3)) +
        6 * β / (N * (1 - M.discount) ^ 2)

/-- Lemma 3.8, `lem:properties-M01-lower-generative`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1747–1767`, for the parameters
`p = (4γ-1)/(3γ)` and `α = 32(1-γ)²ε/(9γ²)` of `eq:choise-p-alpha-lower-bound-generative`
(lines 1731–1734). `M₀` and `M₁` are the source two-state, one-action MDPs with `p_M = p` and
`p_M = p + α` (`hardMDP`, state `true` = `s₁`); `Q⋆(s₁, a)` is the trajectory Q-value of the
optimal greedy policy at the single action `()`. Clause (ii) is stated for any proofs that `p`
and `p + α` lie in `[0,1]`, which clause (i) supplies. -/
def Lemma3_8 : Prop :=
  ∀ (γ ε : ℝ), (2 : ℝ) / 3 ≤ γ → ∀ (hγ1 : γ < 1), 0 < ε → ε < 1 / (32 * (1 - γ)) →
    let p : ℝ := (4 * γ - 1) / (3 * γ)
    let α : ℝ := 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)
    (1 / 2 ≤ p ∧ p < p + α ∧ p + α < 1 ∧ 2 * α ≤ 1 - p) ∧
    (∀ (hγ0 : 0 ≤ γ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ p + α) (hq1 : p + α ≤ 1),
      let M₀ := StatisticalRL.GenerativeLowerBound.hardMDP γ p hγ0 hγ1 hp0 hp1
      let M₁ := StatisticalRL.GenerativeLowerBound.hardMDP γ (p + α) hγ0 hγ1 hq0 hq1
      2 * ε < M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true () -
        M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ()) ∧
    (α ^ 2 / (1 - p) = 32 ^ 2 * (1 - γ) ^ 3 * ε ^ 2 / (27 * γ ^ 3) ∧
      α ^ 2 / (1 - p) ≤ 128 * (1 - γ) ^ 3 * ε ^ 2)

/-- Corrected Theorem 3.7, `theorem:azar`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1443–1464` (proof 1838–2173).
The printed theorem is false on its displayed domain; see `docs/SOURCE-ISSUES.md`, entries
"Candidate C1: singleton actions in Theorem 3.7(i)", "Candidate C2: one state and known rewards
in Theorem 3.7" and "Candidate repair of Theorem 3.7". This entry differs from the print in
exactly three ways:
1. `S ≥ 2` is assumed in both parts (both parts fail for `S = 1` under the known-reward
   convention, C2);
2. `A ≥ 2` is assumed in part (i) only (part (i) fails for `A = 1`, C1); part (ii) covers every
   `A` with `SA ≥ 16`;
3. the estimators are deterministic: `piHat` and `QHat` are arbitrary functions of the known
   reward table, the known discount (source conventions, `generative_model_model_based.tex:31`,
   `prelim.tex:42`) and the `N`-per-state-action sample array (`samplingLaw`, independent draws
   from the true transition rows). Randomized estimators are not covered by this entry; library
   versions for them exist only for `S, A ≥ 2` (`sourcePolicyAndQ_risk_quarter_with_common_constant`).
The witness MDP has states `Fin S`, actions `Fin A` and discount `γ`, and is chosen after the
estimator, separately in each part. `Q^π̂` is the actual forced-first-action trajectory Q of the
returned deterministic policy, `Q⋆` the trajectory Q of the optimal greedy policy (equal to the
optimality fixed point, so tie-independent), `‖·‖` the sup norm, and the events are strict
(`> ε`). The constant `c_N` is chosen before all other quantities (the proof uses `1/32768`);
`N = 0` is allowed. -/
def Thm3_7_corrected : Prop :=
  ∃ c_N : ℝ, 0 < c_N ∧
    ∀ (S A N : ℕ) (γ ε : ℝ),
      2 ≤ S → 16 ≤ S * A →
      (2 : ℝ) / 3 ≤ γ → γ < 1 → 0 < ε → ε < 1 / (32 * (1 - γ)) →
      (N : ℝ) ≤ c_N * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2) →
      (2 ≤ A →
        ∀ piHat : (Fin S → Fin A → ℝ) → ℝ →
            StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin A) N → Fin S → Fin A,
          ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
            (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
              {data | ε < ‖M.trajectoryExpectedQ
                  (fun s ↦ EnvironmentStage.pointMass (piHat M.reward M.discount data s)) -
                M.trajectoryExpectedQ M.optimalGreedyPolicy‖}) ∧
      (∀ QHat : (Fin S → Fin A → ℝ) → ℝ →
            StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin A) N → Fin S → Fin A → ℝ,
          ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
            (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
              {data | ε < ‖QHat M.reward M.discount data -
                M.trajectoryExpectedQ M.optimalGreedyPolicy‖})

/-- Approximate-planner extension of source `Thm:sample-compl-main`,
`source/upstream/tex/chapters/generative_model_model_based.tex:900–923`,
as claimed in the prose paragraph at
`source/upstream/tex/chapters/generative_model_model_based.tex:943`
(a prose claim, not a numbered result): the guarantee of Theorem 3.2 (both
the V clause and the Q clause, with the same δ, ε range, budget and
logarithm) continues to hold, after increasing the universal constant c₀, for
every deterministic policy `f` whose empirical value is within
`1 / (N (1 - γ))` of the empirical optimal value `V̂⋆` in sup norm.
Here `V̂⋆` is `valueEstimator`, the empirical trajectory value of the greedy
empirical-optimal policy (source MB:1005). The policy `f` is quantified inside
the event, so the guarantee applies to any data-dependent planner output.
As for `Thm3_2_positiveN`, the sample count is explicitly positive, see
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). -/
def Thm3_2_approxPlanner_positiveN : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ ε : ℝ),
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    c₀ * Real.log
      (Fintype.card State * Fintype.card Action * N /
        ((1 - M.discount) ^ 2 * ε * δ)) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
    1 - δ ≤
      (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ f : State → Action,
          ‖StatisticalRL.ModelBasedPolicyLearning.valueEstimator M N hN data -
            (StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).trajectoryExpectedValue
              (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
              1 / (N * (1 - M.discount)) →
            (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
              M.trajectoryExpectedValue
                (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
            (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
                M.discount * ε ≤
              M.trajectoryExpectedQ
                (fun t ↦ EnvironmentStage.pointMass (f t)) s a)}

/-- Planning-cost claim of the prose paragraph
`source/upstream/tex/chapters/generative_model_model_based.tex:943`, following
source `Thm:sample-compl-main`,
`source/upstream/tex/chapters/generative_model_model_based.tex:900–923`; a prose
claim, not a numbered result. The source says empirical VI and PI reach the slack
`‖V̂⋆ − V̂^π̂‖∞ ≤ 1/(N(1−γ))` within `O((1−γ)⁻¹ log(N/(1−γ)))` iterations.
The `O(·)` is rendered by one universal constant `C` chosen before the model,
sample count and data. The source does not fix the initialization or tie
rule; here:
* VI: any initialization `Q₀` with entries in `[0, 1/(1−γ)]` (e.g. `Q₀ = 0`),
  `k` applications of the empirical Bellman optimality operator, then any
  greedy selector `f` of the `k`-th iterate;
* PI: any initial stationary policy `π 0` and arbitrary greedy tie choices;
  the guarantee is for the `k`-th policy `π k`, `k ≥ 1`.
The hypothesis `0 < N` is implicit in the printed claim, which divides by `N`
(the slack is `1/(N(1−γ))`); no suffix is used. -/
def Thm3_2_planningIterations : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
      (data : StatisticalRL.ModelBasedPolicyLearning.Samples State Action N),
    letI : Nonempty Action := M.action_nonempty
    (∀ Q₀ : State → Action → ℝ,
      (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) →
      ∀ k : ℕ, C / (1 - M.discount) * Real.log (N / (1 - M.discount)) ≤ k →
      ∀ f : State → Action,
        (∀ s, ((StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).qOptimality^[k]
            Q₀) s (f s) =
          actionMaximum
            (((StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).qOptimality^[k]
              Q₀) s)) →
        ‖StatisticalRL.ModelBasedPolicyLearning.valueEstimator M N hN data -
          (StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount))) ∧
    (∀ (π : ℕ → StationaryPolicy State Action) (g : ℕ → State → Action),
      (∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (g n s)) →
      (∀ n s, (StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).policyFixedPoint
          (π n) s (g n s) =
        actionMaximum
          ((StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).policyFixedPoint
            (π n) s)) →
      ∀ k : ℕ, 1 ≤ k → C / (1 - M.discount) * Real.log (N / (1 - M.discount)) ≤ k →
        ‖StatisticalRL.ModelBasedPolicyLearning.valueEstimator M N hN data -
          (StatisticalRL.ModelBasedPolicyLearning.empiricalModel M N hN data).trajectoryExpectedValue
            (π k)‖ ≤ 1 / (N * (1 - M.discount)))

end StatisticalRL.Statements.Ch3
