import Formalization.Generative.ModelBasedPolicyLearning
import Formalization.Generative.PolicyEvaluationPerturbation
import Formalization.Generative.PolicyEvaluationHoeffding
import Formalization.Probability.EmpiricalHoeffdingFamily

/-! A deterministic comparison for the empirical greedy policy. -/

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

open MeasureTheory ProbabilityTheory
local instance hoeffdingLearningStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance hoeffdingLearningStateDecidable : DecidableEq State := Classical.decEq State


/-- Every state-action row has its true independent product sampling law. -/
theorem samplingLaw_stateActionRow (M : DiscountedMDP State Action)
    (N : ℕ) (s : State) (a : Action) :
    (samplingLaw M N).map (fun data i ↦ data ((s,a),i)) =
      (M.transition s a).sampleMeasure N := by
  let f : Fin N → (State × Action) × Fin N := fun i ↦ ((s,a),i)
  have hf : Function.Injective f := by intro i j h; exact Prod.mk.inj h |>.2
  have hind := (samplingLaw_independent M N).precomp hf
  have hm : ∀ i : Fin N, AEMeasurable (fun data : Samples State Action N ↦ data ((s,a),i))
      (samplingLaw M N) := fun i ↦ (measurable_pi_apply ((s,a),i)).aemeasurable
  rw [(iIndepFun_iff_map_fun_eq_pi_map hm).mp hind]
  unfold FiniteDistribution.sampleMeasure
  congr 1
  funext i
  exact samplingLaw_marginal M N ((s,a),i)

/-- A fixed nonnegative test vector satisfies Hoeffding under the actual
state-action product experiment. -/
theorem samplingLaw_row_hoeffding (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (s : State) (a : Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (V : State → ℝ) (hV : ∀ s, 0 ≤ V s) :
    (samplingLaw M N).real {data |
      FiniteDistribution.familyRadius N 1 δ V <
        |(empiricalRow N hN data s a).expectation V -
          (M.transition s a).expectation V|} < δ := by
  let d := M.transition s a
  have ht := d.familyViolation_lt N 1 hN (by norm_num) δ hδ hδ1 V hV
  have hmeas : MeasurableSet (d.familyViolation N hN 1 δ V) :=
    (Set.to_countable _).measurableSet
  rw [← samplingLaw_stateActionRow M N s a, measureReal_def,
    Measure.map_apply (measurable_of_countable _) hmeas] at ht
  simp only [Nat.cast_one, div_one] at ht
  exact ht

/-- Simultaneous concentration over all deterministic policies and rows. -/
theorem samplingLaw_all_policy_rows_hoeffding (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ (f : State → Action) (s : State) (a : Action),
      |(empiricalRow N hN data s a).expectation
          (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))) -
        (M.transition s a).expectation
          (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)))| ≤
      FiniteDistribution.familyRadius N 1
        (δ / Fintype.card ((State → Action) × State × Action))
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)))} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let I := (State → Action) × State × Action
  let m : ℝ := Fintype.card I
  let η := δ / m
  let μ := samplingLaw M N
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hη : 0 < η := div_pos hδ hm
  have hη1 : η < 1 := by dsimp [η]; rw [div_lt_iff₀ hm]; linarith
  let bad (i : I) : Set (Samples State Action N) := {data |
    FiniteDistribution.familyRadius N 1 η
      (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (i.1 t))) <
      |(empiricalRow N hN data i.2.1 i.2.2).expectation
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (i.1 t))) -
       (M.transition i.2.1 i.2.2).expectation
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (i.1 t)))|}
  have hb (i : I) : μ.real (bad i) < η := by
    exact samplingLaw_row_hoeffding M N hN i.2.1 i.2.2 η hη hη1 _
      (fun s ↦ (M.trajectoryExpectedValue_bounds _ s).1)
  have hall : μ.real (⋃ i : I, bad i) < δ := by
    calc
      _ ≤ ∑ i : I, μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ < ∑ _i : I, η := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ hb i)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change m * η = δ
        dsimp [η]
        field_simp
  let good : Set (Samples State Action N) := {data | ∀ (f : State → Action) (s : State) (a : Action),
      |(empiricalRow N hN data s a).expectation
          (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))) -
        (M.transition s a).expectation
          (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)))| ≤
      FiniteDistribution.familyRadius N 1 η
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)))}
  have hsub : (⋃ i : I, bad i)ᶜ ⊆ good := by
    intro data hd f s a
    exact not_lt.mp (fun h ↦ hd (Set.mem_iUnion.mpr ⟨(f,s,a), h⟩))
  have hmono := measureReal_mono hsub (measure_ne_top μ good)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ i : I, bad i)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ < μ.real good
  linarith

/-- For a deterministic policy, the policy residual is the corresponding row residual. -/
theorem deterministic_policy_residual (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N)
    (f : State → Action) (s : State) :
    DiscountedMDP.policyValueResidual M (empiricalModel M N hN data)
      (fun t ↦ EnvironmentStage.pointMass (f t)) s =
      (empiricalRow N hN data s (f s)).expectation
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))) -
      (M.transition s (f s)).expectation
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))) := by
  unfold DiscountedMDP.policyValueResidual DiscountedMDP.policyTransition
  rw [FiniteDistribution.expectation_bind, FiniteDistribution.expectation_bind]
  simp only [EnvironmentStage.expectation_pointMass]
  rfl

/-- Empirical optimality transfers to the true MDP with the sum of the
    evaluation errors for the true-optimal and empirical-optimal policies. -/
theorem policyEstimator_loss_le_evaluation_errors
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (s : State) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass
        (policyEstimator M N hN data t)) s ≤
      ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
          M.trajectoryExpectedValue M.optimalGreedyPolicy‖ +
      ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) -
        M.trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t))‖ := by
  let H := empiricalModel M N hN data
  let π := fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)
  have hopt : H.trajectoryExpectedValue M.optimalGreedyPolicy s ≤
      H.trajectoryExpectedValue π s := by
    exact policyEstimator_empirical_optimal M N hN data M.optimalGreedyPolicy s
  have h₁ := norm_le_pi_norm (H.trajectoryExpectedValue M.optimalGreedyPolicy -
    M.trajectoryExpectedValue M.optimalGreedyPolicy) s
  have h₂ := norm_le_pi_norm (H.trajectoryExpectedValue π - M.trajectoryExpectedValue π) s
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h₁ h₂
  have h₁' := neg_abs_le (H.trajectoryExpectedValue M.optimalGreedyPolicy s -
    M.trajectoryExpectedValue M.optimalGreedyPolicy s)
  have h₂' := le_abs_self (H.trajectoryExpectedValue π s - M.trajectoryExpectedValue π s)
  change M.trajectoryExpectedValue M.optimalGreedyPolicy s -
    M.trajectoryExpectedValue π s ≤ _
  linarith


/-- Uniform transition residuals for deterministic policies yield a loss bound.
The universal quantifier allows the empirical greedy policy to depend on the data. -/
theorem policyEstimator_loss_le_uniform_residual
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (ε : ℝ) (hε : 0 ≤ ε)
    (hres : ∀ f : State → Action, ∀ s,
      |DiscountedMDP.policyValueResidual M (empiricalModel M N hN data)
        (fun t ↦ EnvironmentStage.pointMass (f t)) s| ≤ ε)
    (s : State) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass
        (policyEstimator M N hN data t)) s ≤
      2 * (M.discount * ε / (1 - M.discount)) := by
  let H := empiricalModel M N hN data
  let π := fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)
  have h₁ := DiscountedMDP.trajectoryValue_perturbation_bound_of_residual M H
    M.optimalGreedyPolicy rfl rfl ε hε (hres M.optimalGreedyAction)
  have h₂ := DiscountedMDP.trajectoryValue_perturbation_bound_of_residual M H
    π rfl rfl ε hε (hres (policyEstimator M N hN data))
  have h := policyEstimator_loss_le_evaluation_errors M N hN data s
  change M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue π s ≤
      ‖H.trajectoryExpectedValue M.optimalGreedyPolicy -
        M.trajectoryExpectedValue M.optimalGreedyPolicy‖ +
      ‖H.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ at h
  linarith

/-- A conservative explicit policy-learning guarantee under the genuine joint
sampling law. The finite union ranges over deterministic policies and rows. -/
theorem policyEstimator_hoeffding (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ s,
      M.trajectoryExpectedValue M.optimalGreedyPolicy s -
        M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass
          (policyEstimator M N hN data t)) s ≤
      2 * M.discount / (1 - M.discount) ^ 2 *
        Real.sqrt (Real.log (2 * Fintype.card ((State → Action) × State × Action) / δ) / (2 * N))} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let m : ℝ := Fintype.card ((State → Action) × State × Action)
  let q := Real.sqrt (Real.log (2 * m / δ) / (2 * N))
  let ε := (1 / (1 - M.discount)) * q
  have hm : m ≠ 0 := by dsimp [m]; exact_mod_cast Fintype.card_ne_zero
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hε : 0 ≤ ε := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hr (f : State → Action) :
      FiniteDistribution.familyRadius N 1 (δ / m)
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))) ≤ ε := by
    unfold FiniteDistribution.familyRadius
    have hn := ModelBasedPolicyEvaluation.truePolicyValue_norm_bound M
      (fun t ↦ EnvironmentStage.pointMass (f t))
    have hid : Real.sqrt (Real.log (2 / (δ / m)) / (2 * N)) = q := by
      dsimp [q]
      congr 2
      field_simp
    norm_num only [Nat.cast_one]

    rw [hid]
    exact mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _)
  let good₁ : Set (Samples State Action N) := {data | ∀ (f : State → Action) (s : State) (a : Action),
      |(empiricalRow N hN data s a).expectation
          (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))) -
        (M.transition s a).expectation
          (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)))| ≤
      FiniteDistribution.familyRadius N 1 (δ / m)
        (M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)))}
  let good₂ : Set (Samples State Action N) := {data | ∀ s,
      M.trajectoryExpectedValue M.optimalGreedyPolicy s -
        M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass
          (policyEstimator M N hN data t)) s ≤
      2 * M.discount / (1 - M.discount) ^ 2 * q}
  have hs : 1 - δ < (samplingLaw M N).real good₁ :=
    samplingLaw_all_policy_rows_hoeffding M N hN δ hδ hδ1
  have hsub : good₁ ⊆ good₂ := by
    intro data hdata s
    have hres (f : State → Action) (t : State) :
        |DiscountedMDP.policyValueResidual M (empiricalModel M N hN data)
          (fun t ↦ EnvironmentStage.pointMass (f t)) t| ≤ ε := by
      rw [deterministic_policy_residual]
      exact (hdata f t (f t)).trans (hr f)
    have hh := policyEstimator_loss_le_uniform_residual M N hN data ε hε hres s
    calc
      _ ≤ 2 * (M.discount * ε / (1 - M.discount)) := hh
      _ = 2 * M.discount / (1 - M.discount) ^ 2 * q := by dsimp [ε]; field_simp
  have hmono := measureReal_mono hsub (measure_ne_top (samplingLaw M N) good₂)
  change 1 - δ < (samplingLaw M N).real good₂
  linarith

end StatisticalRL.ModelBasedPolicyLearning
