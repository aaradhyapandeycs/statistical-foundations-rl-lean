import Formalization.Statements.Ch3
import Formalization.Generative.GenerativeLowerBoundTwoStateMDP
import Formalization.Generative.PolicyLearningVarianceResolventBridge
import Formalization.Generative.PolicyLearningAnyOptimalPolicy
import Formalization.Generative.PolicyEvaluationUniversalConstant
import Formalization.Generative.PolicyLearningMainSample
import Formalization.Generative.PolicyLearningAbsorbingPreservation
import Formalization.Generative.PolicyLearningAbsorbingGrid
import Formalization.Generative.PolicyLearningSourcePointwise
import Formalization.Generative.FiniteHorizonMainSample
import Formalization.Generative.GenerativeLowerBoundTheorem37Fin

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

end StatisticalRL.Statements.Ch3
