import Formalization.Generative.PolicyLearningJointEvaluation

/-! Source evaluation lemma with its explicit pointwise optimality inequalities. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance sourcePointwiseStateMeasurable : MeasurableSpace State := ⊤

/-- Source-shaped simultaneous V bounds, with concrete shared constants
c₀ = 720 and c₁ = 16, uniformly over all exact empirical optimizers. -/
theorem source_policyLearning_evaluation_with_pointwise (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlarge : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N) :
    1 - δ < (samplingLaw M N).real {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
          16 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
        ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
          2 * 16 * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
        ∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
          M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤
            2 * 16 * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))} := by
  let q := Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
  let r₀ := Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
  let r₁ := 2 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
    6 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 2)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hb : 0 ≤ leaveOneOutBeta M N δ :=
    le_trans (by norm_num) (leaveOneOutBeta_ge_four M N hN δ hδ hδ1)
  have hroot : q ≤ Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by
    apply Real.sqrt_le_sqrt
    have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hx : 0 ≤ leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3) := by positivity
    have heq : 2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3) =
        2 * (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by ring
    rw [heq]
    linarith
  have hr := sourceEvaluation_concrete_radius_bounds M N hN δ hδ hδ1 hlarge
  change r₀ ≤ 27 * q ∧ r₁ ≤ 5 * q at hr
  have hfitted : r₁ ≤ 16 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by linarith
  have hsum : r₀ + r₁ ≤ 2 * 16 * q := by linarith [hr.1, hr.2]
  let good : Set (Samples State Action N) := {data |
      ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
        M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ r₀ ∧
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ r₁ ∧
        (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
          M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ r₀ + r₁) ∧
        (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ≤ M.discount * (r₀ + r₁))}
  have hp : 1 - δ < (samplingLaw M N).real good := joint_policyEvaluation_event M N hN δ hδ hδ1 hlarge
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top (samplingLaw M N) _)
  intro data hd f hf
  obtain ⟨he, hv, _⟩ := hd.2 f hf
  refine ⟨he.trans hfitted, ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro s
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (hv s).1] using (hv s).2.trans hsum
  · intro s
    exact ⟨(hv s).1, (hv s).2.trans hsum⟩

/-- Lean's totalized logarithm makes the unguarded N=0 threshold vacuous. -/
theorem leaveOneOutBeta_zero_samples (M : DiscountedMDP State Action) (δ : ℝ) :
    leaveOneOutBeta M 0 δ = 0 := by
  simp [leaveOneOutBeta, Real.log_zero]

theorem zero_samples_satisfy_unguarded_threshold (M : DiscountedMDP State Action)
    (δ c₀ : ℝ) : c₀ * leaveOneOutBeta M 0 δ / (1 - M.discount) ≤ (0 : ℕ) := by
  simp [leaveOneOutBeta_zero_samples]

/-- One concrete universal pair precedes all source parameters; the sample
count is positive as part of the source sampling/log domain. -/
theorem source_policyLearning_pointwise_universal_constants :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ : ℝ),
      0 < δ → δ < 1 → c₀ * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N →
      1 - δ < (samplingLaw M N).real {data |
        ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
          ‖(empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t)) -
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
            c₁ * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
          ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
            2 * c₁ * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
          ∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
              M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
            M.trajectoryExpectedValue M.optimalGreedyPolicy s -
              M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤
              2 * c₁ * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))} := by
  refine ⟨720, 16, by norm_num, by norm_num, ?_⟩
  intro State Action _ _ M N hN δ hδ hδ1 hlarge
  exact source_policyLearning_evaluation_with_pointwise M N hN δ hδ hδ1 hlarge

end StatisticalRL.ModelBasedPolicyLearning
