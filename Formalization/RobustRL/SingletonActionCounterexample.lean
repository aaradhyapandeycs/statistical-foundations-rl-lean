import Formalization.RobustRL.ChiSquaredPolicyValue
import Formalization.Probability.EmpiricalRow
import Mathlib.Probability.Independence.Basic

/-!
# Singleton-action obstruction for robust χ² policy lower bounds

This module records a restricted-domain counterexample using the project's
stationary randomized policy-value interface and the actual independent
product law of nominal transition rows. At S=2 and A=1, a fixed estimator has
zero strict robust-loss probability for every model pair, while the displayed
positive-radius/sample-budget constraints are feasible at γ=3/4, ρ=1, N=1.

This is a source-scope review artifact, not a formalization of the complete
minimax theorem and not author-approved errata. Its conclusion applies only
to the stationary-policy representation implemented by
`ChiSquaredPolicyValue`.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.RobustRL.SingletonActionCounterexample

abbrev State := Fin 2
abbrev Action := Fin 1
abbrev SampleIndex := (State × Action) × Fin 1
abbrev Sample := SampleIndex → State
abbrev Estimator := (State → Action → ℝ) → ℝ → Sample → StationaryPolicy State Action

local instance stateMeasurable : MeasurableSpace State := ⊤
local instance actionMeasurable : MeasurableSpace Action := ⊤


/-- A concrete nonempty nominal model at the chosen dimensions and discount. -/
noncomputable def witnessNominalMDP : DiscountedMDP State Action where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition := fun _ _ ↦ EnvironmentStage.pointMass (0 : State)
  reward := fun _ _ ↦ 0
  reward_nonneg := by intros; norm_num
  reward_le_one := by intros; norm_num
  discount := 3 / 4
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- A second concrete nominal model with the same known reward and discount
but different transition rows. -/
noncomputable def witnessAlternativeMDP : DiscountedMDP State Action where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition := fun _ _ ↦ EnvironmentStage.pointMass (1 : State)
  reward := fun _ _ ↦ 0
  reward_nonneg := by intros; norm_num
  reward_le_one := by intros; norm_num
  discount := 3 / 4
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- The two nominal witnesses are genuinely different, despite sharing the
known reward and discount. -/
theorem witnessNominalMDPs_distinct : witnessNominalMDP ≠ witnessAlternativeMDP := by
  intro h
  have hprob := congrArg (fun M : DiscountedMDP State Action =>
    (M.transition (0 : State) (0 : Action)).prob (0 : State)) h
  norm_num [witnessNominalMDP, witnessAlternativeMDP, EnvironmentStage.pointMass] at hprob

/-- A concrete positive-radius robust model for the parameter witness. -/
noncomputable def witnessRMDP : ChiSquaredRMDP (State := State) (Action := Action) where
  nominal := witnessNominalMDP
  radius := 1
  radius_pos := by norm_num

/-- The second concrete robust model has the same radius. -/
noncomputable def witnessAlternativeRMDP : ChiSquaredRMDP (State := State) (Action := Action) where
  nominal := witnessAlternativeMDP
  radius := 1
  radius_pos := by norm_num

/-- A concrete initial distribution for the witness. -/
noncomputable def witnessInitialDistribution : FiniteDistribution State :=
  EnvironmentStage.pointMass (0 : State)

/-- One actual transition observation for each state-action row. -/
noncomputable def nominalSampleLaw
    (R : ChiSquaredRMDP (State := State) (Action := Action)) : Measure Sample :=
  Measure.pi (fun i : SampleIndex ↦
    (R.nominal.transition i.1.1 i.1.2).rowMeasure)

instance nominalSampleLaw_probability
    (R : ChiSquaredRMDP (State := State) (Action := Action)) :
    IsProbabilityMeasure (nominalSampleLaw R) := by
  unfold nominalSampleLaw
  infer_instance

/-- Each coordinate is drawn from the corresponding nominal transition row. -/
theorem nominalSampleLaw_marginal
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (i : SampleIndex) :
    (nominalSampleLaw R).map (fun data ↦ data i) =
      (R.nominal.transition i.1.1 i.1.2).rowMeasure := by
  exact (measurePreserving_eval
    (fun i : SampleIndex ↦ (R.nominal.transition i.1.1 i.1.2).rowMeasure) i).map_eq

/-- The complete finite sample array is independent under the actual product
of nominal transition-row laws. -/
theorem nominalSampleLaw_independent
    (R : ChiSquaredRMDP (State := State) (Action := Action)) :
    iIndepFun (fun i (data : Sample) ↦ data i) (nominalSampleLaw R) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- The printed numerical side conditions are feasible for any positive
universal constants c₃ and c₄ at S=2,A=1,γ=3/4,ρ=1,N=1. -/
theorem sourceParameters_feasible
    (c₃ c₄ : ℝ) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ c₃ / (1 - (3 : ℝ) / 4) ∧
      (1 : ℝ) ≤ c₄ /
        ((1 - (3 : ℝ) / 4) ^ 3 * ε ^ 2) *
          (1 + (1 : ℝ) / (1 - (3 : ℝ) / 4)) := by
  let ε := min (4 * c₃) (Real.sqrt (320 * c₄))
  have hc₃pos : 0 < 4 * c₃ := by positivity
  have hsqrtarg : 0 < 320 * c₄ := by positivity
  have hsqrt : 0 < Real.sqrt (320 * c₄) := Real.sqrt_pos.2 hsqrtarg
  have hεpos : 0 < ε := lt_min hc₃pos hsqrt
  have hεleft : ε ≤ 4 * c₃ := min_le_left _ _
  have hεright : ε ≤ Real.sqrt (320 * c₄) := min_le_right _ _
  have hεsq : ε ^ 2 ≤ 320 * c₄ := by
    have hsqrt_sq : (Real.sqrt (320 * c₄)) ^ 2 = 320 * c₄ :=
      Real.sq_sqrt hsqrtarg.le
    nlinarith
  refine ⟨ε, hεpos, ?_, ?_⟩
  · have hdiscount : (1 : ℝ) - (3 : ℝ) / 4 = 1 / 4 := by norm_num
    rw [hdiscount]
    have hdiv : c₃ / (1 / 4 : ℝ) = 4 * c₃ := by
      field_simp
    rw [hdiv]
    exact hεleft
  · have hdiscount : (1 : ℝ) - (3 : ℝ) / 4 = 1 / 4 := by norm_num
    have hden : (1 / 4 : ℝ) ^ 3 * ε ^ 2 = ε ^ 2 / 64 := by
      rw [show (1 / 4 : ℝ) ^ 3 = 1 / 64 by norm_num]
      ring
    have hfactor : 1 + (1 : ℝ) / (1 / 4 : ℝ) = 5 := by norm_num
    simp only [hdiscount]
    rw [hden, hfactor]
    have hεsqpos : 0 < ε ^ 2 := pow_pos hεpos 2
    have hscaled : ε ^ 2 / 64 ≤ 5 * c₄ := by nlinarith [hεsq]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (div_pos hεsqpos (by norm_num : (0 : ℝ) < 64))).2
    nlinarith

/-- Under the actual product sample law, every estimator into stationary
randomized policies has zero robust-loss probability on a singleton-action
space. The statement is uniform over all admissible nominal models and all
initial distributions; it does not require a particular data-dependent rule. -/
theorem singletonAction_policyRisk_zero
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) (ε : ℝ) (hε : 0 < ε)
    (estimator : Estimator) :
    (nominalSampleLaw R).real {data |
      ε < chiSquaredRobustOptimalValueAtDistribution R μ -
        chiSquaredRobustPolicyValueAtDistribution R
          (estimator R.nominal.reward R.nominal.discount data) μ} = 0 := by
  have hzero := chiSquaredRobustPolicyFailureMeasure_eq_zero_of_subsingleton
    R μ (nominalSampleLaw R) (fun data ↦
      estimator R.nominal.reward R.nominal.discount data) hε
  simpa [Measure.real, hzero]

/-- For any pair of robust models, with no selected discount or radius
premises, both stationary policy-estimation risks vanish under their actual,
model-specific product sample laws. The source-parameter witness below adds
the particular discount and radius; this general lemma needs neither. -/
theorem singletonAction_pairRisk_zero
    (R₀ R₁ : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) (ε : ℝ) (hε : 0 < ε)
    (estimator : Estimator) :
    (nominalSampleLaw R₀).real {data |
      ε < chiSquaredRobustOptimalValueAtDistribution R₀ μ -
        chiSquaredRobustPolicyValueAtDistribution R₀
          (estimator R₀.nominal.reward R₀.nominal.discount data) μ} = 0 ∧
    (nominalSampleLaw R₁).real {data |
      ε < chiSquaredRobustOptimalValueAtDistribution R₁ μ -
        chiSquaredRobustPolicyValueAtDistribution R₁
          (estimator R₁.nominal.reward R₁.nominal.discount data) μ} = 0 := by
  constructor
  · exact singletonAction_policyRisk_zero R₀ μ ε hε estimator
  · exact singletonAction_policyRisk_zero R₁ μ ε hε estimator

/-- The two-model maximum risk is zero for every stationary-policy estimator. -/
theorem singletonAction_pairMaxRisk_zero
    (R₀ R₁ : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) (ε : ℝ) (hε : 0 < ε)
    (estimator : Estimator) :
    max
      ((nominalSampleLaw R₀).real {data |
        ε < chiSquaredRobustOptimalValueAtDistribution R₀ μ -
          chiSquaredRobustPolicyValueAtDistribution R₀
            (estimator R₀.nominal.reward R₀.nominal.discount data) μ})
      ((nominalSampleLaw R₁).real {data |
        ε < chiSquaredRobustOptimalValueAtDistribution R₁ μ -
          chiSquaredRobustPolicyValueAtDistribution R₁
            (estimator R₁.nominal.reward R₁.nominal.discount data) μ}) = 0 := by
  rcases singletonAction_pairRisk_zero R₀ R₁ μ ε hε estimator with ⟨h₀, h₁⟩
  rw [h₀, h₁]
  norm_num

/-- The concrete witness satisfies the source's fixed dimensions, discount,
positive radius, and all required nonemptiness conditions. -/
theorem witness_parameters :
    Fintype.card State = 2 ∧ Fintype.card Action = 1 ∧
      witnessNominalMDP.discount = (3 : ℝ) / 4 ∧ witnessRMDP.radius = 1 ∧
      witnessAlternativeMDP.discount = (3 : ℝ) / 4 ∧ witnessAlternativeRMDP.radius = 1 := by
  norm_num [State, Action, witnessNominalMDP, witnessRMDP,
    witnessAlternativeMDP, witnessAlternativeRMDP]

/-- A data-independent estimator is in the source policy-estimator class. -/
noncomputable def witnessEstimator : Estimator :=
  fun _ _ _ ↦ witnessNominalMDP.optimalGreedyPolicy

/-- At feasible source parameters the concrete model pair and estimator have
zero maximum strict-error risk, hence are incompatible with a positive lower
bound on this source subdomain (within the stationary-policy interface). -/
theorem witness_pair_maxRisk_lt_eighth
    (c₃ c₄ : ℝ) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ c₃ / (1 - (3 : ℝ) / 4) ∧
      (1 : ℝ) ≤ c₄ /
        ((1 - (3 : ℝ) / 4) ^ 3 * ε ^ 2) *
          (1 + (1 : ℝ) / (1 - (3 : ℝ) / 4)) ∧
      (Fintype.card State = 2 ∧ Fintype.card Action = 1 ∧
        witnessNominalMDP.discount = (3 : ℝ) / 4 ∧ witnessRMDP.radius = 1 ∧
        witnessAlternativeMDP.discount = (3 : ℝ) / 4 ∧
        witnessAlternativeRMDP.radius = 1) ∧
      max
        ((nominalSampleLaw witnessRMDP).real {data |
          ε < chiSquaredRobustOptimalValueAtDistribution witnessRMDP witnessInitialDistribution -
            chiSquaredRobustPolicyValueAtDistribution witnessRMDP
              (witnessEstimator witnessRMDP.nominal.reward witnessRMDP.nominal.discount data)
              witnessInitialDistribution})
        ((nominalSampleLaw witnessAlternativeRMDP).real {data |
          ε < chiSquaredRobustOptimalValueAtDistribution witnessAlternativeRMDP witnessInitialDistribution -
            chiSquaredRobustPolicyValueAtDistribution witnessAlternativeRMDP
              (witnessEstimator witnessAlternativeRMDP.nominal.reward witnessAlternativeRMDP.nominal.discount data)
              witnessInitialDistribution}) < 1 / 8 := by
  obtain ⟨ε, hε, hεupper, hN⟩ := sourceParameters_feasible c₃ c₄ hc₃ hc₄
  refine ⟨ε, hε, ?_, hN, witness_parameters, ?_⟩
  · norm_num at hεupper ⊢
    nlinarith
  · rw [singletonAction_pairMaxRisk_zero witnessRMDP witnessAlternativeRMDP
      witnessInitialDistribution ε hε witnessEstimator]
    norm_num

/-- The feasible radius/accuracy witness defeats the source-style existential
model-pair conclusion for one fixed estimator: every pair of robust models
on this singleton-action space has zero maximum risk. -/
theorem witnessEstimator_allPairs_lt_eighth
    (c₃ c₄ : ℝ) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ c₃ / (1 - (3 : ℝ) / 4) ∧
      (1 : ℝ) ≤ c₄ /
        ((1 - (3 : ℝ) / 4) ^ 3 * ε ^ 2) *
          (1 + (1 : ℝ) / (1 - (3 : ℝ) / 4)) ∧
      ∀ (R₀ R₁ : ChiSquaredRMDP (State := State) (Action := Action))
        (μ : FiniteDistribution State),
        max
          ((nominalSampleLaw R₀).real {data |
            ε < chiSquaredRobustOptimalValueAtDistribution R₀ μ -
              chiSquaredRobustPolicyValueAtDistribution R₀
                (witnessEstimator R₀.nominal.reward R₀.nominal.discount data) μ})
          ((nominalSampleLaw R₁).real {data |
            ε < chiSquaredRobustOptimalValueAtDistribution R₁ μ -
              chiSquaredRobustPolicyValueAtDistribution R₁
                (witnessEstimator R₁.nominal.reward R₁.nominal.discount data) μ}) < 1 / 8 := by
  obtain ⟨ε, hε, hεupper, hN⟩ := sourceParameters_feasible c₃ c₄ hc₃ hc₄
  refine ⟨ε, hε, ?_, hN, ?_⟩
  · norm_num at hεupper ⊢
    nlinarith
  · intro R₀ R₁ μ
    rw [singletonAction_pairMaxRisk_zero R₀ R₁ μ ε hε witnessEstimator]
    norm_num

end StatisticalRL.RobustRL.SingletonActionCounterexample
