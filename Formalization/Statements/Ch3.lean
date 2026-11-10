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

/-- First-attempt policy-evaluation bound `eq:eq:Vhatpi-Vpi-difference-decoupled-Hoeffding`
(the label's doubled `eq:` is dropped in the Lean name),
`source/upstream/tex/chapters/generative_model_model_based.tex:270–276` (estimator
`eq:defn-empirical-P-policy-eval` and `eq:value-estimation-MB-inf-vhat`, :90–106; first-attempt
analysis, :173–276): there is a universal constant `C₀ > 0` such that, for all finite
state and action spaces, every model, every stationary policy `π`, every `N ≥ 1` and every
`δ ∈ (0,1)`, with probability exceeding `1 − δ` (strict, as printed),
`‖V̂^π − V^π‖∞ ≤ C₀(√(log(S/δ)/((1−γ)⁴N)) + log(S/δ)/((1−γ)²N))`. `V̂^π` is the plug-in
value of the empirical policy kernel built from `N` samples per state (`valueEstimator`, as in
`Thm3_1`) and `V^π` the expected infinite-trajectory value. `N > 0` is a binder because the
printed display divides by `N` and the empirical-frequency model needs it. The result is
stated, not the printed Hoeffding proof route; the Lean proof derives it from the
policy-evaluation export of `Thm3_1` (with `δ/2`), the crude bound
`‖V̂^π − V^π‖∞ ≤ 1/(1−γ)`, and the exact case `S = 1`. -/
def Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (S A N : ℕ) (hN : 0 < N)
    (M : DiscountedMDP (Fin S) (Fin A)) (π : StationaryPolicy (Fin S) (Fin A)) (δ : ℝ),
    0 < δ → δ < 1 →
    1 - δ < (StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M π N).real
      {data | ‖StatisticalRL.ModelBasedPolicyEvaluation.valueEstimator M π N hN data -
          M.trajectoryExpectedValue π‖ ≤
        C₀ * (Real.sqrt (Real.log (S / δ) / ((1 - M.discount) ^ 4 * N)) +
          Real.log (S / δ) / ((1 - M.discount) ^ 2 * N))}

/-- `eqn:ice-cream`, `source/upstream/tex/chapters/generative_model_model_based.tex:619–634`
(display `:626–630`, its premise `N ≥ β₁/(1−γ)` at `:633`, `β₁ = C₀ log(Sm/δ)` at `:478` and
`:634`, `m = ⌈log(e/(1−γ))⌉` at `:624`/`:634`). Printed: for some large enough constant `C₀`,
with probability exceeding `1 − δ`, `‖V̂^π − V^π‖∞ ≤ 3√(8β₁/((1−γ)³N))`, provided
`N ≥ β₁/(1−γ)`. "Some large enough `C₀`" is read as `∃ C̄ > 0, ∀ C₀ ≥ C̄`. `V̂^π` is the plug-in
value of the empirical policy kernel (`valueEstimator`, as in `Thm3_1`) and `V^π` the expected
infinite-trajectory value; `N > 0` is a binder since the display divides by `N`. The printed
display is a chain; its middle expression `2√(8β₁/((1−γ)³N)) + 2β₁/((1−γ)²N)` is a proof step
derived under Step 6's working premise `N ≥ 64β₁/(1−γ)` (`:622`), and this entry states the
labelled final bound under the display's own premise. The premise `N ≥ β₁/(1−γ)` is kept as printed; the library
export proves the bound for every `N ≥ 1` and every `C₀ ≥ 8`, using this project's repair of the printed proof gap
between `N ≥ β₁/(1−γ)` and `N ≥ 64β₁/(1−γ)` (`docs/SOURCE-ISSUES.md`, C3). -/
def Eqn_ice_cream : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ C₀ : ℝ, C ≤ C₀ →
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (N : ℕ) (hN : 0 < N) (δ : ℝ), 0 < δ → δ < 1 →
      let m : ℕ := ⌈Real.log (Real.exp 1 / (1 - M.discount))⌉₊
      let β₁ : ℝ := C₀ * Real.log ((Fintype.card State : ℝ) * (m : ℝ) / δ)
      β₁ / (1 - M.discount) ≤ N →
      1 - δ < (StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M π N).real
        {data | ‖StatisticalRL.ModelBasedPolicyEvaluation.valueEstimator M π N hN data -
            M.trajectoryExpectedValue π‖ ≤
          3 * Real.sqrt (8 * β₁ / ((1 - M.discount) ^ 3 * N))}

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

/-- Source `Thm:sample-compl-main`,
`source/upstream/tex/chapters/generative_model_model_based.tex:900–923` (algorithm
`alg:policy-learn-model-based`, :814–865), as printed: no positivity premise on the per-pair
sample size `N`. The quantifiers are those of the source: a universal `c₀ > 0`, then any finite
state/action spaces, model, `N`, `0 < δ < 1` and `0 < ε ≤ 1/(1−γ)` with
`N ≥ c₀ log(SAN/((1−γ)²εδ))/((1−γ)³ε²)` (`EqnSamples-main`). The guarantee is stated for every
deterministic policy `f` that is optimal for the empirical MDP `M̂` ("any optimal deterministic
policy returned by" the algorithm), quantified inside the event; `V⋆`, `Q⋆` are the values of
the true model's optimal greedy policy.

Domain of definition (typing guard, not a restriction): at `N = 0` the printed statement is
undefined, since the threshold contains `log(SAN/…)` with `SAN = 0` and the empirical model
`P̂(s'|s,a) = (1/N)∑ᵢ 1{sᵢ = s'}` is `0/0`. The Lean empirical model therefore needs a proof
`hN : 0 < N`, and the event quantifies over that witness: at `N = 0` the event is the whole
sample space, so the `N = 0` case carries no content, exactly as in the source where it is not
in the domain. For `N > 0` this entry is equivalent to `Thm3_2_positiveN`. -/
def Thm3_2 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (N : ℕ) (δ ε : ℝ),
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    c₀ * Real.log
      (Fintype.card State * Fintype.card Action * N /
        ((1 - M.discount) ^ 2 * ε * δ)) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
    1 - δ ≤
      (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ hN : 0 < N, ∀ f : State → Action,
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
For the same positive-size empirical data, a grid point covers the empirical
optimal value V̂⋆ within one grid step. -/
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

/-- Source `lem:policy-learning-evaluation`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1306–1326`, as printed: no
positivity premise on the per-pair sample size `N`. Universal constants `c₀, c₁ > 0`; for any
finite state/action spaces, model, `N` and `0 < δ < 1`, with
`β₁ = 2 log(16SAN/((1−γ)δ))` (`leaveOneOutBeta`, `eq:beta-policy-learning`) and
`N ≥ c₀β₁/(1−γ)`, with probability at least `1 − δ`, every deterministic policy `f` optimal for
the empirical MDP (`π̂⋆`, no tie rule fixed, quantified inside the event) satisfies
`‖V̂^{π̂⋆} − V^{π̂⋆}‖∞ ≤ c₁√(2β₁/(N(1−γ)³))` and
`0 ≤ V⋆ − V^{π̂⋆} ≤ 2c₁√(β₁/(N(1−γ)³))` pointwise, simultaneously.

Domain of definition (typing guard, not a restriction): at `N = 0` the printed statement is
undefined, since `β₁` contains `log(16SAN/…)` with `SAN = 0`, both bounds divide by `N`, and the
empirical model `P̂` (hence `V̂^{π̂⋆}` and `π̂⋆`) is `0/0`. The Lean empirical model needs a
proof `hN : 0 < N`, and the event quantifies over that witness, so at `N = 0` the event is the
whole sample space and that case carries no content, as in the source where it is outside the
domain. For `N > 0` this entry is equivalent to `Lemma3_5_positiveN`. -/
def Lemma3_5 : Prop :=
  ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (N : ℕ) (δ : ℝ),
    0 < δ → δ < 1 →
    c₀ * StatisticalRL.ModelBasedPolicyLearning.leaveOneOutBeta M N δ /
      (1 - M.discount) ≤ N →
    1 - δ ≤
      (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ hN : 0 < N, ∀ f : State → Action,
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
fallback action from the first environment stage. The general result, for every
deterministic policy that is optimal for the empirical MDP at every stage and state
(no tie rule fixed), is `Thm3_9_positiveN`; this entry is its special case for the
concrete backward-greedy tie rule. -/
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
/-- `eq:lemma-VarP-V-bound` together with `eq:I-gamma-P-Var-bound`,
`source/upstream/tex/chapters/generative_model_model_based.tex:300–352` (`eq:I-gamma-P-Var-bound`
`:327–341`, `eq:lemma-VarP-V-bound` `:346–352`). For every finite MDP and stationary policy `π`,
with `P_π(s,t) = Σ_a π(a|s)P(t|s,a)`, `V^π` the expected infinite-trajectory value,
`Var_{P_π}(V^π)(s)` the variance of `V^π` under the row `P_π(s,·)` and `(I − γP_π)⁻¹` the matrix
inverse: `0 ≤ (I − γP_π)⁻¹Var_{P_π}(V^π) ≤ (2‖V^π‖∞²/γ²)1` entrywise, and
`0 ≤ ‖(I − γP_π)⁻¹√Var_{P_π}(V^π)‖∞ ≤ √(2/(1−γ))‖V^π‖∞/γ`. Domain condition `0 < γ`: the printed
bounds divide by `γ` (at `γ = 0` they are undefined; Lean's `x/0 = 0` would make them false).
The intermediate expressions of the printed chain are proof steps and are not stated. -/
def Eq_lemma_VarP_V_bound : Prop :=
  ∀ (State Action : Type*) [Fintype State] [Fintype Action] [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action),
    0 < M.discount →
    let P : Matrix State State ℝ := fun s t ↦ (M.policyTransition π s).prob t
    let V : State → ℝ := M.trajectoryExpectedValue π
    let VarV : State → ℝ := fun s ↦ (M.policyTransition π s).variance V
    let R : Matrix State State ℝ := (1 - M.discount • P)⁻¹
    (∀ s, 0 ≤ (R *ᵥ VarV) s ∧ (R *ᵥ VarV) s ≤ 2 * ‖V‖ ^ 2 / M.discount ^ 2) ∧
    0 ≤ ‖R *ᵥ (fun s ↦ Real.sqrt (VarV s))‖ ∧
    ‖R *ᵥ (fun s ↦ Real.sqrt (VarV s))‖ ≤
      Real.sqrt (2 / (1 - M.discount)) * ‖V‖ / M.discount

open scoped Matrix in
/-- Lemma 3.6, `lem:empirical-value-residual`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1395–1410`, on the event
`eq:Bernstein-empirical-optimal-value` (`chapters/generative_model_model_based.tex:1373–1376`). `π̂⋆` is any deterministic policy
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
(`chapters/generative_model_model_based.tex:1730–1735`). `M₀` and `M₁` are the source two-state, one-action MDPs with `p_M = p` and
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
3. part (i) is stated for deterministic estimators returning deterministic policies (`piHat` is a
   function, not a kernel).
Part (ii) covers every Q-function estimator, randomized included: `QHat` assigns to the known
reward table, the known discount (source conventions, `generative_model_model_based.tex:31`,
`prelim.tex:42`) and the `N`-per-state-action sample array (`samplingLaw`, independent draws from
the true transition rows) a probability measure on Q-tables `Fin S → Fin A → ℝ`. The measurable
structure on Q-tables is the Borel σ-algebra (product of the Borel σ-algebra of `ℝ`; this is the
instance the file resolves to, guarded by an `example` below), so the error sets are open, hence
measurable, and the failure probability is the genuine joint probability
`∫ data, (QHat r γ data).real {Q | ε < ‖Q - Q⋆‖} ∂samplingLaw`. Deterministic estimators are the
Dirac case `QHat r γ data = δ_{Q̂(r,γ,data)}`, which recovers the deterministic statement.
The witness MDP has states `Fin S`, actions `Fin A` and discount `γ`, and is chosen after the
estimator, separately in each part. `Q^π̂` is the actual forced-first-action trajectory Q of the
returned deterministic policy, `Q⋆` the trajectory Q of the optimal greedy policy (equal to the
optimality fixed point, so tie-independent), `‖·‖` the sup norm, and the events are strict
(`> ε`). The constant `c_N` is chosen before all other quantities (the proof uses `1/32768`,
unchanged by the randomization); `N = 0` is allowed. -/
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
            StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin A) N →
              Measure (Fin S → Fin A → ℝ),
          (∀ r g data, IsProbabilityMeasure (QHat r g data)) →
          ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
            (1 : ℝ) / 4 ≤ ∫ data, (QHat M.reward M.discount data).real
                {Q | ε < ‖Q - M.trajectoryExpectedQ M.optimalGreedyPolicy‖}
              ∂(StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N))

/-- Single-action (policy-evaluation) case of `theorem:azar` part (ii),
`source/upstream/tex/chapters/generative_model_model_based.tex:1443–1464`, in the form used by the
comparisons "policy evaluation setting with `A = 1`" (`generative_model_model_based.tex:1468–1474`)
and "setting `A = 1` therein" (`generative_model_model_free.tex:248–249`). With `A = 1` the printed
domain `SA ≥ 16` is `S ≥ 16`; the printed ranges `γ ∈ [2/3, 1)`, `0 < ε < 1/(32(1−γ))` and
`N ≤ c_N log(SA)/((1−γ)³ε²)` are kept (`log(S·1) = log S`). With one action there is a unique
policy `π₀ = (s ↦ δ₀)` and `Q⋆(s,0) = V^{π₀}(s)`, so the entry is stated in policy-evaluation
form: the estimator `VHat` receives the known reward table, the known discount and `N` independent
draws from the policy row at each state (`ModelBasedPolicyEvaluation.samplingLaw`, the sampling
of Theorem 3.1 and of TD learning) and returns a probability measure on value vectors
`Fin S → ℝ` (every estimator, randomized included; Borel σ-algebra, the instance the file resolves
to, guarded by an `example` below; Dirac measures give deterministic estimators). The error is
`‖V − V^{π₀}‖∞` with `V^{π₀}` the expected infinite-trajectory value, and the failure probability
is the joint probability `∫ data, (VHat r γ data).real {V | ε < ‖V - V^{π₀}‖} ∂samplingLaw`.
Differences from the print: none. The corrections C1 and C2 of `Thm3_7_corrected` are vacuous here
(`S ≥ 16 ≥ 2`, part (i) not included). The constant `c_N` is chosen first (the proof uses
`1/32768`), the witness MDP after the estimator; `N = 0` is allowed and the event is strict
(`> ε`). -/
def Thm3_7_policyEvaluation_A1 : Prop :=
  ∃ c_N : ℝ, 0 < c_N ∧
    ∀ (S N : ℕ) (γ ε : ℝ),
      16 ≤ S → (2 : ℝ) / 3 ≤ γ → γ < 1 → 0 < ε → ε < 1 / (32 * (1 - γ)) →
      (N : ℝ) ≤ c_N * Real.log (S : ℝ) / ((1 - γ) ^ 3 * ε ^ 2) →
      ∀ VHat : (Fin S → Fin 1 → ℝ) → ℝ →
          StatisticalRL.ModelBasedPolicyEvaluation.Samples (Fin S) N → Measure (Fin S → ℝ),
        (∀ r g data, IsProbabilityMeasure (VHat r g data)) →
        ∃ M : DiscountedMDP (Fin S) (Fin 1), M.discount = γ ∧
          (1 : ℝ) / 4 ≤ ∫ data, (VHat M.reward M.discount data).real
              {V | ε < ‖V - M.trajectoryExpectedValue
                (fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1))‖}
            ∂(StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M
              (fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1)) N)

/-- Restricted reading of the burn-in necessity claim `eq:sample-size-range-planning`,
`source/upstream/tex/chapters/generative_model_model_based.tex:930–940`: "Condition
`N ≥ Ω̃(1/(1−γ))` is necessary for learning a policy that performs strictly better than a random
guess". The book does not define "random guess"; this entry reads "strictly better" as value gap
at most `1/(64(1−γ))`, a constant fraction of the trivial range `1/(1−γ)`. It does not cover
accuracies between `1/(64(1−γ))` and `1/(1−γ)`. Further restrictions, inherited from
`Thm3_7_corrected`: `S ≥ 2`, `A ≥ 2`, `SA ≥ 16`, `γ ≥ 2/3`, and deterministic estimators only
(`piHat` is any function of the known rewards, the known discount and the `N`-per-pair sample
array). The success metric is the book's `V⋆ − V^{π̂}` in sup norm, with `V⋆` the trajectory value
of the optimal greedy policy (equal to the optimal value, so tie-independent) and `V^{π̂}` the
trajectory value of the returned deterministic policy. The constant `c` is chosen first; the
witness MDP after the estimator. See `docs/SOURCE-ISSUES.md#C49`. -/
def Thm3_2_burnInNecessary_restricted : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S A N : ℕ) (γ : ℝ),
      2 ≤ S → 2 ≤ A → 16 ≤ S * A → (2 : ℝ) / 3 ≤ γ → γ < 1 →
      (N : ℝ) ≤ c * Real.log ((S : ℝ) * (A : ℝ)) / (1 - γ) →
      ∀ piHat : (Fin S → Fin A → ℝ) → ℝ →
          StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin A) N → Fin S → Fin A,
        ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
          (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
            {data | 1 / (64 * (1 - γ)) <
              ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
                M.trajectoryExpectedValue
                  (fun s ↦ EnvironmentStage.pointMass (piHat M.reward M.discount data s))‖}

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

/-- Two-state, one-action Q-estimation lower bound, displays
`eq:N-UB-test-lower-Q-generative-overall` and `eq:P-Mi-Q-inaccurate-lower-generative`,
`source/upstream/tex/chapters/generative_model_model_based.tex:1541–1556` (proof 1557–1835).
For every `γ ∈ [2/3, 1)` and `0 < ε < 1/(32(1−γ))` there are two MDPs `M₀, M₁` with states
`Bool` (`true` is `s₁`) and the single action `()`, sharing the discount `γ` and the known
reward table, chosen before `N` and the estimator as printed. For every `N` with
`N ≤ 0.003/((1−γ)³ε²)` (`N = 0` included) and every estimator `Q̂`, some `Mᵢ` has
`P_{Mᵢ}(|Q̂(s₁,a) − Q⋆_{Mᵢ}(s₁,a)| > ε) > 0.1`. Here `Q⋆` is the trajectory Q function of the
optimal greedy policy. The estimator is any (randomized) function of the full sample array (`N`
independent generative draws for each state-action pair, both rows, `samplingLaw`): `QHat data` is
a probability measure on `ℝ` (Borel σ-algebra, the instance the file resolves to, guarded by an
`example` below), and the probability is the joint data/estimate probability
`∫ data, (QHat data).real {y | ε < |y − Q⋆|} ∂samplingLaw`. Deterministic estimators are the Dirac
case. No deviation from the printed display. The strict `> 0.1` uses the Pinsker branch
(SOURCE-ISSUES C4 records the omitted strictness step of the printed proof). -/
def Eq_P_Mi_Q_inaccurate_lower_generative : Prop :=
  ∀ (γ ε : ℝ), (2 : ℝ) / 3 ≤ γ → γ < 1 → 0 < ε → ε < 1 / (32 * (1 - γ)) →
    ∃ M₀ M₁ : DiscountedMDP Bool Unit,
      M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
      ∀ N : ℕ, (N : ℝ) ≤ 0.003 / ((1 - γ) ^ 3 * ε ^ 2) →
      ∀ QHat : StatisticalRL.ModelBasedPolicyLearning.Samples Bool Unit N → Measure ℝ,
        (∀ data, IsProbabilityMeasure (QHat data)) →
        (1 : ℝ) / 10 < ∫ data, (QHat data).real
            {y | ε < |y - M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true ()|}
            ∂(StatisticalRL.ModelBasedPolicyLearning.samplingLaw M₀ N) ∨
        (1 : ℝ) / 10 < ∫ data, (QHat data).real
            {y | ε < |y - M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true ()|}
            ∂(StatisticalRL.ModelBasedPolicyLearning.samplingLaw M₁ N)

/-! Guard for the three randomized entries above: under this file's local instances the
σ-algebras on Q-tables, value vectors and reals are the Borel ones, not the local `⊤`. -/
example : (inferInstance : MeasurableSpace (Fin 3 → Fin 2 → ℝ)) = MeasurableSpace.pi := rfl
example : (inferInstance : MeasurableSpace (Fin 3 → ℝ)) = MeasurableSpace.pi := rfl
example : (inferInstance : MeasurableSpace ℝ) = Real.measurableSpace := rfl

/-- Matching lower bound behind the prose claim at
`source/upstream/tex/chapters/generative_model_model_based.tex:2585` (paragraph :2573–2585) that
the sample size `SAH⁴/ε²` of Theorem 3.9 (`eq:sample-size-finite-horizon-generative`, :2580–2583;
`Thm:sample-compl-finite`, :2551–2570) "is provably minimax optimal". Formal reading of a prose
claim; the book states no lower-bound theorem and cites `domingues2021episodic` for it. The proof
here is our own and uses the book's own online hard family (`chapters/onlineRL.tex:2512–3075`,
`onlineLBStages`) with generative sampling; it does not establish the cited paper's theorem
(total, possibly non-uniform or adaptive, sample budget), which is not covered.

Protocol (the book's, :23–30 and :2533–2540): rewards known; the sample array holds `N`
independent next-state draws from `P_h(·|s,a)` for every stage `h`, state `s` and action `a`
(non-adaptive, uniform), so the total is `H·S·A·N`. The bound is on the per-tuple count:
`N ≤ c·H³/ε²`, i.e. total `≤ c·SAH⁴/ε²`. In this protocol the factor `S·A` comes from the protocol
and is not separately tested: the hard instances use only copy `0` of the family (states `0` and
`⌊S/2⌋`) and the actions `0, 1`.

Estimators (randomized): a seed from an arbitrary probability space `(Seed, ν)` (any universe),
independent of the samples, and a map `piHat` of the seed, the known reward tables and the sample
array to a deterministic nonstationary policy (`ℕ → Fin S → Fin A`, step `h` from `0`); for each
seed value the output is a deterministic policy, so estimators that output a stochastic Markov
policy are not covered (the book's `π̂⋆` is deterministic). Disclosed requirement: every output
action is a measurable function of the seed, for every reward table (not only the hard family's),
data array, step and state; this makes the event below measurable. Deterministic estimators are
the case `Seed = Unit`.

Conclusion: on some instance `E` (chosen after the estimator), with joint probability at least
`1/8` over samples and seed, the output policy fails `ε`-optimality at stage `1` (index `0`) at
some state, i.e. Theorem 3.9's V-guarantee `V_1^{π̂}(s) ≥ V_1⋆(s) − ε` fails. The failure
probability `1/8` is fixed (no `δ`-dependent lower bound is claimed), and the per-tuple threshold
`c·H³/ε²` has no logarithmic factor; it matches Theorem 3.9's `H³ log(HSA/δ)/ε²` per tuple up to
that factor, which is the "up to logarithmic factors" reading of the prose.

Restricted (named `_restricted`; scope disclosure, see
`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): the domain, protocol, deterministic
policy outputs, seed measurability and fixed failure probability above narrow the prose claim.
Domain:
`S, A, H ≥ 2` and `0 < ε ≤ c₁·H` with an existential `c₁`; each exclusion is necessary (for `H = 1`,
`A = 1`, `S = 1` or `ε ≥ H` zero samples suffice). Witnesses in the proof: `c = 2⁻²⁸`,
`c₁ = 1/4096`. -/
def Thm3_9_minimaxLowerBound_restricted : Prop :=
  ∃ c c₁ : ℝ, 0 < c ∧ 0 < c₁ ∧
    ∀ (S A H N : ℕ) (ε : ℝ), 2 ≤ S → 2 ≤ A → 2 ≤ H → 0 < ε → ε ≤ c₁ * H →
      (N : ℝ) ≤ c * (H : ℝ) ^ 3 / ε ^ 2 →
      ∀ (Seed : Type*) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (piHat : Seed → (Fin H → Fin S → Fin A → ℝ) →
          StatisticalRL.FiniteHorizonGenerative.Samples (Fin S) (Fin A) H N →
          ℕ → Fin S → Fin A),
        (∀ r data h s, Measurable (fun ω ↦ piHat ω r data h s)) →
        ∃ E : Fin H → EnvironmentStage (Fin S) (Fin A),
          (1 : ℝ) / 8 ≤ ((StatisticalRL.FiniteHorizonGenerative.samplingLaw E N).prod ν).real
            {p | ∃ s, ε < EnvironmentStage.optimalValue (List.ofFn E) s -
              StatisticalRL.FiniteHorizonGenerative.policyTrajectorySuffix (List.ofFn E)
                (piHat p.2 (fun h s a ↦ (E h).reward s a) p.1) 0 s}

/-- Source `Thm:sample-compl-finite`,
`source/upstream/tex/chapters/generative_model_model_based.tex:2551–2570` (algorithm at
lines 2524–2546), for every deterministic policy `f` that is optimal for the empirical MDP
`M̂` at every stage and state. This is the monograph's notion of an optimal deterministic
policy, `source/upstream/tex/chapters/prelim.tex:738–739`; the algorithm's step 2 does not
fix a tie rule. The policy is quantified inside the event, so every data-dependent tie rule,
causal or not, is covered. Stage `h` is 0-based and `f h` acts at stage `h`; the printed
`V_h^{π̂⋆}(s) ≥ V_h^⋆(s) − ε` is written as `V_h^⋆(s) − V_h^{f}(s) ≤ ε`.

`N > 0` is explicit for the empirical-frequency model, as in `Thm3_2_positiveN`; see
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures).
No content is lost: `S, A, H ≥ 1` are forced (nonempty stage types, `0 < ε ≤ H`), so for
`N = 0` the printed threshold forces `log(HSA/δ) ≤ 0`, hence `δ ≥ HSA ≥ 1`, where the claim is
trivial. The printed form without the `N > 0` binder is `Thm3_9`.

Proof route (differs from the source, which decouples the stages through the causality
of its backward-induction planner, lines 2547–2549): the library proves the statistical
guarantee for a causal "worst-tie" planner that, among the empirically optimal actions,
picks one minimizing the true-model continuation. That planner reads the true model, so it
is an analysis device, not the algorithm. Every empirically optimal `f` dominates it in the
true model at every stage and state, which transfers the bound to `f`. -/
def Thm3_9_positiveN : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (H : ℕ) (E : Fin H → EnvironmentStage State Action)
      (N : ℕ) (hN : 0 < N) (δ ε : ℝ),
      0 < δ → 0 < ε → ε ≤ H →
      c₀ * (H : ℝ) ^ 3 *
        Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N →
      1 - δ ≤
        (StatisticalRL.FiniteHorizonGenerative.samplingLaw E N).real
          {data | ∀ f : ℕ → State → Action,
            (∀ h : Fin H, ∀ s,
              StatisticalRL.FiniteHorizonGenerative.policyTrajectorySuffix
                  (StatisticalRL.FiniteHorizonGenerative.empiricalStages E N hN data) f h.val s =
                EnvironmentStage.optimalValue
                  ((StatisticalRL.FiniteHorizonGenerative.empiricalStages E N hN data).drop
                    h.val) s) →
            ∀ h : Fin H,
              (∀ s,
                EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s -
                  StatisticalRL.FiniteHorizonGenerative.policyTrajectorySuffix (List.ofFn E) f
                    h.val s ≤ ε) ∧
              (∀ s a,
                EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a -
                  StatisticalRL.FiniteHorizonGenerative.policyTrajectoryQSuffix (List.ofFn E) f
                    h.val s a ≤ ε)}

/-- Source `Thm:sample-compl-finite`,
`source/upstream/tex/chapters/generative_model_model_based.tex:2551–2570` (algorithm at
lines 2524–2546), as printed: no positivity premise on the per-tuple sample size `N`. The
quantifiers are those of the source: a universal `c₀`, then any finite state/action spaces,
horizon `H`, stages `E`, sample size `N`, `δ > 0` and `0 < ε ≤ H` with
`N ≥ c₀ H³ log(HSA/δ)/ε²`. The guarantee is stated for every deterministic policy `f` that is
optimal for the empirical MDP `M̂` at every stage and state (the monograph's notion of an
optimal deterministic policy, `source/upstream/tex/chapters/prelim.tex:738–739`; the
algorithm's step 2 fixes no tie rule), quantified inside the event. Stage `h` is 0-based and
`f h` acts at stage `h`; the printed `V_h^{π̂⋆}(s) ≥ V_h^⋆(s) − ε` is written as
`V_h^⋆(s) − V_h^{f}(s) ≤ ε`, and likewise for `Q`.

The empirical model `M̂` (empirical frequencies) is defined only for `N > 0`, so the event
quantifies over a witness `hN : 0 < N`. The printed threshold has no `N` inside the logarithm,
so it is a defined condition at `N = 0`. `S, A ≥ 1` and `H ≥ 1` are forced (nonempty stage
types, `0 < ε ≤ H`), so at `N = 0` the printed threshold implies `δ ≥ HSA ≥ 1` and the claim is
trivial there; the entry is never vacuous. For `N > 0` this entry is exactly `Thm3_9_positiveN`. -/
def Thm3_9 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (State Action : Type*) [Fintype State] [Fintype Action]
      (H : ℕ) (E : Fin H → EnvironmentStage State Action)
      (N : ℕ) (δ ε : ℝ),
      0 < δ → 0 < ε → ε ≤ H →
      c₀ * (H : ℝ) ^ 3 *
        Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N →
      1 - δ ≤
        (StatisticalRL.FiniteHorizonGenerative.samplingLaw E N).real
          {data | ∀ hN : 0 < N, ∀ f : ℕ → State → Action,
            (∀ h : Fin H, ∀ s,
              StatisticalRL.FiniteHorizonGenerative.policyTrajectorySuffix
                  (StatisticalRL.FiniteHorizonGenerative.empiricalStages E N hN data) f h.val s =
                EnvironmentStage.optimalValue
                  ((StatisticalRL.FiniteHorizonGenerative.empiricalStages E N hN data).drop
                    h.val) s) →
            ∀ h : Fin H,
              (∀ s,
                EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s -
                  StatisticalRL.FiniteHorizonGenerative.policyTrajectorySuffix (List.ofFn E) f
                    h.val s ≤ ε) ∧
              (∀ s a,
                EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a -
                  StatisticalRL.FiniteHorizonGenerative.policyTrajectoryQSuffix (List.ofFn E) f
                    h.val s a ≤ ε)}

end StatisticalRL.Statements.Ch3
