import Formalization.Statements.Ch3
import Formalization.Generative.GenerativeLowerBoundTwoStateMDP
import Formalization.Generative.PolicyLearningVarianceResolventBridge
import Formalization.Generative.PolicyLearningAnyOptimalPolicy
import Formalization.Generative.PolicyEvaluationUniversalConstant
import Formalization.Generative.PolicyLearningMainSample
import Formalization.Generative.PolicyLearningApproxPlannerMain
import Formalization.Generative.PlanningEmpirical
import Formalization.Generative.PolicyLearningAbsorbingPreservation
import Formalization.Generative.PolicyLearningAbsorbingGrid
import Formalization.Generative.PolicyLearningSourcePointwise
import Formalization.Generative.FiniteHorizonMainSample
import Formalization.Generative.FiniteHorizonAnyTieSample
import Formalization.Generative.GenerativeLowerBoundTheorem37Fin
import Formalization.Generative.FiniteHorizonLowerBoundTheorem
import Formalization.Generative.GenerativeLowerBoundObservationLaw
import Formalization.Generative.PolicyEvaluationCrude
import Formalization.Generative.BurnInNecessity
import Formalization.Generative.PolicyEvaluationGapRepairAllStates
import Formalization.Generative.PolicyEvaluationVarianceResolvent

/-! Proofs of the source-facing Chapter 3 entries using the existing exports. -/
open MeasureTheory
namespace StatisticalRL.Statements.Ch3

theorem Thm3_1_holds : Thm3_1 :=
  StatisticalRL.ModelBasedPolicyEvaluation.policyEvaluation_universal_constant

theorem Thm3_2_positiveN_holds : Thm3_2_positiveN := by
  obtain ⟨c, hc, hmain⟩ :=
    StatisticalRL.ModelBasedPolicyLearning.mainSample_policyLearning_universal_constant
  refine ⟨c, hc, ?_⟩
  intro State Action _ _ M N hN δ ε hδ hδ1 hε hεmax hsize
  exact (hmain State Action M N hN δ ε hδ hδ1 hε hεmax hsize).le

theorem Lemma3_3_holds : Lemma3_3 := by
  intro State Action _ _ M x s
  exact StatisticalRL.ModelBasedPolicyLearning.optimalValueAbsorbingModel_preserves_optimalTrajectoryValue M x s

theorem Lemma3_4_holds : Lemma3_4 := by
  intro State Action _ _ M N hN data x
  exact StatisticalRL.ModelBasedPolicyLearning.empirical_absorbingGrid_covers_valueEstimator M N hN data x

theorem Lemma3_5_positiveN_holds : Lemma3_5_positiveN := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hmain⟩ :=
    StatisticalRL.ModelBasedPolicyLearning.source_policyLearning_pointwise_universal_constants
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro State Action _ _ M N hN δ hδ hδ1 hsize
  have hp := hmain State Action M N hN δ hδ hδ1 hsize
  refine hp.le.trans (measureReal_mono ?_)
  intro data hd f hf
  exact ⟨(hd f hf).1, (hd f hf).2.2⟩

theorem Thm3_9_causal_positiveN_holds : Thm3_9_causal_positiveN := by
  obtain ⟨c, hc, hmain⟩ :=
    StatisticalRL.FiniteHorizonGenerative.exists_universal_causalFinitePolicy_sample_constant
  refine ⟨c, hc, ?_⟩
  intro State Action _ _ H hH E N hN δ ε hδ hε hεH hsize
  let fallback : Action := Classical.choice (E ⟨0, hH⟩).action_nonempty
  have hp := hmain State Action H E N hN hH fallback δ ε hδ hε hεH hsize
  refine hp.trans (measureReal_mono ?_)
  intro data hd
  dsimp only [StatisticalRL.FiniteHorizonGenerative.CausalPolicyPerformanceEvent] at hd
  dsimp only
  intro h
  exact ⟨fun s ↦ ((hd h.val).1 s).2, fun s a ↦ ((hd h.val).2 s a).2⟩

theorem Lemma3_6_holds : Lemma3_6 := by
  intro State Action _ _ M N hN data f β hβ hf
  have hV := StatisticalRL.ModelBasedPolicyLearning.empiricallyOptimal_value_eq M N hN data f hf
  intro H π Vs hrow
  have hVs : Vs = H.trajectoryExpectedValue π := hV.symm
  rw [hVs] at hrow ⊢
  exact StatisticalRL.DiscountedMDP.empiricalPolicyValue_source_residual_bound M H π rfl rfl
    N hN β hβ hrow

theorem Lemma3_8_holds : Lemma3_8 := by
  intro γ ε hγ hγ1 hε hεmax
  refine ⟨StatisticalRL.GenerativeLowerBound.source_parameters_admissible γ ε hγ hγ1 hε hεmax,
    fun hγ0 hp0 hp1 hq0 hq1 => ?_,
    StatisticalRL.GenerativeLowerBound.source_parameters_squared_ratio γ ε hγ hγ1 hε⟩
  have h0 := StatisticalRL.GenerativeLowerBound.hardMDP_optimalQ_true γ _ hγ0 hγ1 hp0 hp1
  have h1 := StatisticalRL.GenerativeLowerBound.hardMDP_optimalQ_true γ _ hγ0 hγ1 hq0 hq1
  simp only at h0 h1 ⊢
  rw [h0, h1]
  exact StatisticalRL.GenerativeLowerBound.source_parameters_scalar_separation γ ε hγ hγ1 hε hεmax

theorem Thm3_7_corrected_holds : Thm3_7_corrected :=
  ⟨1 / 32768, by norm_num, StatisticalRL.GenerativeLowerBound.theorem37_corrected_fin_carriers⟩

theorem Thm3_2_approxPlanner_positiveN_holds : Thm3_2_approxPlanner_positiveN := by
  obtain ⟨c, hc, hmain⟩ :=
    StatisticalRL.ModelBasedPolicyLearning.mainSample_policyLearning_approx_universal_constant
  refine ⟨c, hc, ?_⟩
  intro State Action _ _ M N hN δ ε hδ hδ1 hε hεmax hsize
  exact (hmain State Action M N hN δ ε hδ hδ1 hε hεmax hsize).le

theorem Thm3_2_planningIterations_holds : Thm3_2_planningIterations :=
  StatisticalRL.ModelBasedPolicyLearning.empirical_planningIterations

theorem Eq_P_Mi_Q_inaccurate_lower_generative_holds : Eq_P_Mi_Q_inaccurate_lower_generative := by
  intro γ ε hγ hγ1 hε hεmax
  refine ⟨StatisticalRL.GenerativeLowerBound.sourceHardMDP γ ε hγ hγ1 hε hεmax false,
    StatisticalRL.GenerativeLowerBound.sourceHardMDP γ ε hγ hγ1 hε hεmax true,
    rfl, rfl, rfl, ?_⟩
  intro N hN QHat
  have hd : 0 < (1 - γ) ^ 3 * ε ^ 2 := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hN' : (N : ℝ) ≤ 9 / (2560 * (1 - γ) ^ 3 * ε ^ 2) := by
    have h9 : (9 : ℝ) / (2560 * (1 - γ) ^ 3 * ε ^ 2) = 9 / 2560 / ((1 - γ) ^ 3 * ε ^ 2) := by
      rw [div_div, mul_assoc]
    rw [h9]
    exact hN.trans (div_le_div_of_nonneg_right (by norm_num : (0.003 : ℝ) ≤ 9 / 2560) hd.le)
  exact StatisticalRL.GenerativeLowerBound.sourceHardMDP_full_Q_estimation_lower
    γ ε hγ hγ1 hε hεmax N hN' (fun data _ _ ↦ QHat data)

theorem Thm3_9_minimaxLowerBound_restricted_holds : Thm3_9_minimaxLowerBound_restricted := by
  refine ⟨1 / 2 ^ 28, 1 / 4096, by norm_num, by norm_num, ?_⟩
  intro S A H N ε hS hA hH hε hεH hN Seed _ ν _ piHat hmeas
  exact StatisticalRL.FiniteHorizonLowerBound.minimaxLowerBound S A H N ε hS hA hH hε hεH hN ν
    piHat fun r data h s a ↦ hmeas r data h s (MeasurableSpace.measurableSet_top (s := {a}))

theorem Thm3_9_positiveN_holds : Thm3_9_positiveN :=
  StatisticalRL.FiniteHorizonGenerative.exists_universal_anyEmpiricalOptimalPolicy_sample_constant

/-- `Thm3_9` from the positive-`N` export: at `N = 0` the event is the whole sample space
(its outer quantifier ranges over proofs of `0 < 0`), so its probability is `1 ≥ 1 − δ`;
for `N > 0` the event contains the export's event. -/
theorem Thm3_9_holds : Thm3_9 := by
  obtain ⟨c₀, hc₀, hmain⟩ :=
    StatisticalRL.FiniteHorizonGenerative.exists_universal_anyEmpiricalOptimalPolicy_sample_constant
  refine ⟨c₀, hc₀, ?_⟩
  intro State Action _ _ H E N δ ε hδ hε hεH hsize
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hprob := StatisticalRL.FiniteHorizonGenerative.samplingLaw_probability E 0
    refine ((by linarith : 1 - δ ≤ 1).trans
      (probReal_univ (μ := StatisticalRL.FiniteHorizonGenerative.samplingLaw E 0)).ge).trans ?_
    exact measureReal_mono (fun _ _ hN0 ↦ absurd hN0 (lt_irrefl 0)) (measure_ne_top _ _)
  · refine (hmain State Action H E N hN δ ε hδ hε hεH hsize).trans ?_
    refine measureReal_mono (fun data hd _ ↦ hd) (measure_ne_top _ _)

theorem Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding_holds :
    Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding :=
  StatisticalRL.ModelBasedPolicyEvaluation.decoupledHoeffding_universal_constant

theorem Eqn_ice_cream_holds : Eqn_ice_cream := by
  refine ⟨8, by norm_num, ?_⟩
  intro C₀ hC₀ State Action _ _ M π N hN δ hδ hδ1 m β₁ _
  exact StatisticalRL.ModelBasedPolicyEvaluation.policyEvaluation_source_radius_all_states_positive_samples
    M π N hN δ C₀ hδ hδ1 hC₀

open scoped Matrix in
theorem Eq_lemma_VarP_V_bound_holds : Eq_lemma_VarP_V_bound := by
  intro State Action _ _ inst M π hγ P V VarV R
  have hinst : inst = Classical.decEq State := Subsingleton.elim _ _
  subst hinst
  have hγ2 : 0 < M.discount ^ 2 := by positivity
  have hg : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  refine ⟨fun s ↦ ?_, norm_nonneg _, ?_⟩
  · obtain ⟨h0, h1⟩ := StatisticalRL.DiscountedMDP.evaluationPolicyResolvent_variance_bound M π s
    change 0 ≤ M.discount ^ 2 * (R *ᵥ VarV) s at h0
    change M.discount ^ 2 * (R *ᵥ VarV) s ≤ ‖V‖ ^ 2 at h1
    refine ⟨nonneg_of_mul_nonneg_right (by linarith) hγ2, ?_⟩
    rw [le_div_iff₀ hγ2]
    nlinarith [sq_nonneg ‖V‖]
  · have h := StatisticalRL.DiscountedMDP.evaluationPolicyResolvent_sqrtVariance_bound M π
    change M.discount * ‖R *ᵥ (fun s ↦ Real.sqrt (VarV s))‖ ≤
      ‖V‖ / Real.sqrt (1 - M.discount) at h
    have h2 : ‖V‖ / Real.sqrt (1 - M.discount) ≤ Real.sqrt (2 / (1 - M.discount)) * ‖V‖ := by
      rw [div_eq_inv_mul, ← Real.sqrt_inv]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.sqrt_le_sqrt
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left (inv_nonneg.mpr hg.le) (by norm_num)
    rw [le_div_iff₀ hγ]
    linarith

theorem Thm3_2_burnInNecessary_restricted_holds : Thm3_2_burnInNecessary_restricted := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro S A N γ hS hA hSA hγ hγ1 hN piHat
  have hN' : (N : ℝ) ≤ Real.log ((S : ℝ) * (A : ℝ)) / (8 * (1 - γ)) := by
    have : 1 / 8 * Real.log ((S : ℝ) * (A : ℝ)) / (1 - γ) =
        Real.log ((S : ℝ) * (A : ℝ)) / (8 * (1 - γ)) := by
      rw [mul_comm (8 : ℝ) (1 - γ), ← div_div]; ring
    rwa [this] at hN
  exact StatisticalRL.GenerativeLowerBound.burnIn_necessary_valueGap S A N γ hS hA hSA hγ hγ1 hN'
    piHat

end StatisticalRL.Statements.Ch3
