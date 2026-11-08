import Formalization.Generative.PolicyLearningJointEvaluation
import Formalization.Probability.VarianceIccPerturbation

/-! # Theorem 3.2 with an approximate empirical planner: evaluation events

Source: the prose claim at
`source/upstream/tex/chapters/generative_model_model_based.tex:943`, extending
`Thm:sample-compl-main` (MB:900–923). The source's proof of Theorem 3.2 uses
exact empirical optimality in the step MB:1015–1026 (eq.
`Vhat-Vstar-pistar-tot` at :1025, argmax justification at :1026), and, in the
library, to identify the fitted policy's empirical value with `V̂⋆` on the
all-rows Bernstein event. Here neither identification is used:

* `approxOptimal_performance` replaces the argmax step by
  `V̂^{π⋆} ≤ V̂⋆ ≤ V̂^f + η`;
* `approxPlanner_row_residual` transfers the policy-free all-rows event for
  `V̂⋆` to the row `(s, f s)` and the vector `V̂^f`, with the doubled
  logarithmic factor `2β`. The mean term uses the sign `V̂^f ≤ V̂⋆`, so it costs
  `η` (not `2η`).

The new evaluation event is stated directly on `‖V̂^f − V^f‖`; it does not
rewrite `V̂^f` into `V̂⋆`. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance approxPlannerStateMeasurable : MeasurableSpace State := ⊤

/-- A point-mass policy's transition variance is the selected row's variance. -/
theorem deterministicPolicyTransition_variance (M : DiscountedMDP State Action)
    (f : State → Action) (s : State) (V : State → ℝ) :
    (M.policyTransition (fun t ↦ EnvironmentStage.pointMass (f t)) s).variance V =
      (M.transition s (f s)).variance V := by
  unfold FiniteDistribution.variance
  rw [deterministicPolicyTransition_expectation, deterministicPolicyTransition_expectation]

/-- Under the planner slack, the empirical value of `f` is sandwiched below the
empirical optimal value `V̂⋆` and within `η` of it. -/
theorem approxPlanner_value_sandwich (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (f : State → Action) (η : ℝ)
    (hslack : ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ η) (s : State) :
    (empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ valueEstimator M N hN data s ∧
      valueEstimator M N hN data s ≤ (empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t)) s + η := by
  refine ⟨policyEstimator_empirical_optimal M N hN data _ s, ?_⟩
  have h := norm_le_pi_norm (valueEstimator M N hN data -
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t))) s
  rw [Pi.sub_apply, Real.norm_eq_abs] at h
  have h' := le_abs_self (valueEstimator M N hN data s -
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) s)
  linarith

/-- Deterministic performance comparison for an `η`-approximate empirical
planner (replacing the exact-argmax step MB:1015–1026). -/
theorem approxOptimal_performance (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (f : State → Action)
    (η ε₀ ε₁ : ℝ)
    (hslack : ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ η)
    (h₀ : ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ ε₀)
    (h₁ : ‖(empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t)) -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ ε₁) :
    (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
       M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
       M.trajectoryExpectedValue M.optimalGreedyPolicy s -
       M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ ε₀ + ε₁ + η) ∧
    (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
       M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
       M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
       M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ≤
         M.discount * (ε₀ + ε₁ + η)) := by
  let H := empiricalModel M N hN data
  let π := fun t ↦ EnvironmentStage.pointMass (f t)
  have hv (s : State) : M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue π s ≤ ε₀ + ε₁ + η := by
    have ho := policyEstimator_empirical_optimal M N hN data M.optimalGreedyPolicy s
    have hsand := (approxPlanner_value_sandwich M N hN data f η hslack s).2
    have ha := norm_le_pi_norm (H.trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy) s
    have hb := norm_le_pi_norm (H.trajectoryExpectedValue π - M.trajectoryExpectedValue π) s
    simp only [Pi.sub_apply, Real.norm_eq_abs] at ha hb
    have ha' := neg_abs_le (H.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue M.optimalGreedyPolicy s)
    have hb' := le_abs_self (H.trajectoryExpectedValue π s - M.trajectoryExpectedValue π s)
    change H.trajectoryExpectedValue M.optimalGreedyPolicy s ≤ valueEstimator M N hN data s at ho
    change valueEstimator M N hN data s ≤ H.trajectoryExpectedValue π s + η at hsand
    linarith
  exact ⟨fun s ↦ ⟨sub_nonneg.mpr (M.trajectoryValue_le_optimalGreedy _ s), hv s⟩,
    fun s a ↦ M.trajectoryQ_loss_le_discount_of_value_loss _ _ hv s a⟩

/-- Row transfer: on the policy-free all-rows event for `V̂⋆`, the residual of
the fitted policy `f` (for its own empirical value `V̂^f`) satisfies the
residual hypothesis of `empiricalPolicyValue_source_error_bound` with the
doubled factor `2β`, provided the planner slack is `η ≤ 1/(N(1−γ))`. -/
theorem approxPlanner_row_residual (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (f : State → Action)
    (β η : ℝ) (hβ : 4 ≤ β) (hη : η ≤ 1 / (N * (1 - M.discount)))
    (hslack : ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ η)
    (hd : ∀ (x : State) (a : Action),
      |(empiricalRow N hN data x a).expectation (valueEstimator M N hN data) -
        (M.transition x a).expectation (valueEstimator M N hN data)| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance (valueEstimator M N hN data)) +
        2 * β / (N * (1 - M.discount)))
    (s : State) :
    |empiricalPolicyValueResidual M (empiricalModel M N hN data)
        (fun t ↦ EnvironmentStage.pointMass (f t)) s| ≤
      Real.sqrt (2 * β / N) * Real.sqrt ((M.policyTransition
        (fun t ↦ EnvironmentStage.pointMass (f t)) s).variance
          ((empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t)))) +
        2 * (2 * β) / (N * (1 - M.discount)) := by
  let H := empiricalModel M N hN data
  let π : StationaryPolicy State Action := fun t ↦ EnvironmentStage.pointMass (f t)
  let V := valueEstimator M N hN data
  let W := H.trajectoryExpectedValue π
  let Pe := empiricalRow N hN data s (f s)
  let P := M.transition s (f s)
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ0 : 0 ≤ β := by linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hslack
  have hsand (x : State) : W x ≤ V x ∧ V x ≤ W x + η :=
    approxPlanner_value_sandwich M N hN data f η hslack x
  -- Mean term, using the sign `W ≤ V`: it costs `η`.
  have hmean (d : FiniteDistribution State) :
      d.expectation W ≤ d.expectation V ∧ d.expectation V ≤ d.expectation W + η := by
    refine ⟨d.expectation_mono fun x ↦ (hsand x).1, ?_⟩
    have h := d.expectation_mono (f := V) (g := fun x ↦ W x + η) fun x ↦ (hsand x).2
    rwa [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const] at h
  have hres : empiricalPolicyValueResidual M H π s = Pe.expectation W - P.expectation W := by
    unfold empiricalPolicyValueResidual
    rw [deterministicPolicyTransition_expectation, deterministicPolicyTransition_expectation]
    rfl
  have hvar : (M.policyTransition π s).variance W = P.variance W :=
    deterministicPolicyTransition_variance M f s W
  change |empiricalPolicyValueResidual M H π s| ≤
    Real.sqrt (2 * β / N) * Real.sqrt ((M.policyTransition π s).variance W) +
      2 * (2 * β) / (N * (1 - M.discount))
  rw [hres, hvar]
  have hrow : |Pe.expectation V - P.expectation V| ≤
      Real.sqrt (β / N) * Real.sqrt (P.variance V) + 2 * β / (N * (1 - M.discount)) :=
    hd s (f s)
  have hm1 := hmean Pe
  have hm2 := hmean P
  have habs : |Pe.expectation W - P.expectation W| ≤
      |Pe.expectation V - P.expectation V| + η := by
    rw [abs_le]
    have h1 := le_abs_self (Pe.expectation V - P.expectation V)
    have h2 := neg_abs_le (Pe.expectation V - P.expectation V)
    constructor <;> linarith [hm1.1, hm1.2, hm2.1, hm2.2]
  -- Variance term: both vectors lie in `[0, 1/(1-γ)]`.
  have hVrange (x : State) : V x ∈ Set.Icc 0 (1 / (1 - M.discount)) :=
    H.trajectoryExpectedValue_bounds _ x
  have hWrange (x : State) : W x ∈ Set.Icc 0 (1 / (1 - M.discount)) :=
    H.trajectoryExpectedValue_bounds _ x
  have hVW (x : State) : |V x - W x| ≤ η := by
    rw [abs_le]
    constructor <;> linarith [hsand x]
  have hvarle : P.variance V ≤ P.variance W + 2 * (1 / (1 - M.discount)) * η :=
    P.variance_le_variance_add_of_Icc hVrange hWrange hVW
  have hsq : Real.sqrt (P.variance V) ≤
      Real.sqrt (P.variance W) + Real.sqrt (2 * (1 / (1 - M.discount)) * η) :=
    (Real.sqrt_le_sqrt hvarle).trans
      (sqrt_add_le_sqrt_add_sqrt (P.variance_nonneg W) (by positivity))
  -- Absorption of the variance perturbation into `β/(N(1-γ))`.
  have hT : Real.sqrt (β / N) * Real.sqrt (2 * (1 / (1 - M.discount)) * η) ≤
      β / (N * (1 - M.discount)) := by
    rw [← Real.sqrt_mul (by positivity)]
    have key : β / N * (2 * (1 / (1 - M.discount)) * η) ≤
        (β / (N * (1 - M.discount))) ^ 2 := by
      calc
        _ ≤ β / N * (2 * (1 / (1 - M.discount)) * (1 / (N * (1 - M.discount)))) := by
          gcongr
        _ = 2 * β / (N * (1 - M.discount)) ^ 2 := by
          field_simp
        _ ≤ β ^ 2 / (N * (1 - M.discount)) ^ 2 := by
          gcongr
          nlinarith
        _ = (β / (N * (1 - M.discount))) ^ 2 := by rw [div_pow]
    calc
      _ ≤ Real.sqrt ((β / (N * (1 - M.discount))) ^ 2) := Real.sqrt_le_sqrt key
      _ = β / (N * (1 - M.discount)) := Real.sqrt_sq (by positivity)
  have hηβ : η ≤ β / (N * (1 - M.discount)) := by
    refine hη.trans ?_
    gcongr
    linarith
  have hroot : Real.sqrt (β / N) ≤ Real.sqrt (2 * β / N) := by
    apply Real.sqrt_le_sqrt
    gcongr
    linarith
  have hsW := Real.sqrt_nonneg (P.variance W)
  have hsβ := Real.sqrt_nonneg (β / N)
  have hprod : Real.sqrt (β / N) * Real.sqrt (P.variance W) ≤
      Real.sqrt (2 * β / N) * Real.sqrt (P.variance W) :=
    mul_le_mul_of_nonneg_right hroot hsW
  have hsplit : Real.sqrt (β / N) * Real.sqrt (P.variance V) ≤
      Real.sqrt (β / N) * Real.sqrt (P.variance W) +
        Real.sqrt (β / N) * Real.sqrt (2 * (1 / (1 - M.discount)) * η) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hsq hsβ
  have he1 : 2 * β / (N * (1 - M.discount)) = 2 * (β / (N * (1 - M.discount))) := by ring
  have he2 : 2 * (2 * β) / (N * (1 - M.discount)) = 4 * (β / (N * (1 - M.discount))) := by
    ring
  rw [he2]
  rw [he1] at hrow
  linarith

/-- The fitted-policy evaluation event for every planner output within the
printed slack `1/(N(1−γ))` of `V̂⋆`, with radius computed from `2β`. The event
is stated directly on `‖V̂^f − V^f‖`; its probability comes from the unchanged
policy-free all-rows event `empiricalOptimalValue_allRows_residual`. -/
theorem all_approxPlanner_evaluation_source_bound
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ∀ f : State → Action,
        ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount)) →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
        2 * Real.sqrt (2 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 3)) +
          6 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 2)} := by
  let μ := samplingLaw M N
  let β := leaveOneOutBeta M N δ
  have hβ : 4 ≤ β := leaveOneOutBeta_ge_four M N hN δ hδ hδ1
  let good : Set (Samples State Action N) := {data |
      ∀ (x : State) (a : Action),
      |(empiricalRow N hN data x a).expectation (valueEstimator M N hN data) -
        (M.transition x a).expectation (valueEstimator M N hN data)| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance (valueEstimator M N hN data)) +
        2 * β / (N * (1 - M.discount))}
  have hs : 1 - δ / 2 < μ.real good := empiricalOptimalValue_allRows_residual M N hN δ hδ hδ1
  let target : Set (Samples State Action N) := {data |
      ∀ f : State → Action,
        ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount)) →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
        2 * Real.sqrt (2 * (2 * β) / (N * (1 - M.discount) ^ 3)) +
          6 * (2 * β) / (N * (1 - M.discount) ^ 2)}
  have hsub : good ⊆ target := by
    intro data hd f hslack
    apply empiricalPolicyValue_source_error_bound M (empiricalModel M N hN data)
      (fun t ↦ EnvironmentStage.pointMass (f t)) rfl rfl N hN (2 * β) (by linarith)
    intro s
    exact approxPlanner_row_residual M N hN data f β (1 / (N * (1 - M.discount))) hβ le_rfl
      hslack hd s
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

/-- Joint event: the true-optimal-policy evaluation event (planner-free) and
the approximate-planner evaluation event hold together with probability
greater than `1 − δ`. On it, every planner output with slack `η ≤ 1/(N(1−γ))`
satisfies the V and Q performance bounds with radius `r₀ + r₁′ + η`. -/
theorem joint_approxPlanner_event (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlarge : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N) :
    1 - δ < (samplingLaw M N).real {data |
      ∀ (f : State → Action) (η : ℝ), η ≤ 1 / (N * (1 - M.discount)) →
        ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ η →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
          2 * Real.sqrt (2 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 3)) +
            6 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 2) ∧
        (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
          M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤
            Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
            (2 * Real.sqrt (2 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 3)) +
              6 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 2)) + η) ∧
        (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ≤
            M.discount *
              (Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
              (2 * Real.sqrt (2 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 3)) +
                6 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 2)) + η))} := by
  let μ := samplingLaw M N
  let r₀ := Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
  let r₁ := 2 * Real.sqrt (2 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 3)) +
    6 * (2 * leaveOneOutBeta M N δ) / (N * (1 - M.discount) ^ 2)
  let A : Set (Samples State Action N) := {data |
    ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ r₀}
  let B : Set (Samples State Action N) := {data |
    ∀ f : State → Action,
      ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount)) →
      ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
        M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ r₁}
  have ha : 1 - δ / 2 < μ.real A := trueOptimalPolicy_beta_event M N hN δ hδ hδ1 hlarge
  have hb : 1 - δ / 2 < μ.real B := all_approxPlanner_evaluation_source_bound M N hN δ hδ hδ1
  have hca := measureReal_compl (μ := μ) ((Set.to_countable A).measurableSet)
  have hcb := measureReal_compl (μ := μ) ((Set.to_countable B).measurableSet)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (Aᶜ ∪ Bᶜ)).measurableSet)
  rw [probReal_univ] at hca hcb hc
  have hu := measureReal_union_le (μ := μ) Aᶜ Bᶜ
  have hi : 1 - δ < μ.real (A ∩ B) := by
    have : (Aᶜ ∪ Bᶜ)ᶜ = A ∩ B := by ext x; simp
    rw [this] at hc
    linarith
  apply hi.trans_le
  apply measureReal_mono _ (measure_ne_top μ _)
  intro data hd f η hη hslack
  have h₁ := hd.2 f (hslack.trans hη)
  exact ⟨h₁, approxOptimal_performance M N hN data f η r₀ r₁ hslack hd.1 h₁⟩

end StatisticalRL.ModelBasedPolicyLearning
