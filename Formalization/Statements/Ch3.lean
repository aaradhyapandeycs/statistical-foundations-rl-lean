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

end StatisticalRL.Statements.Ch3
