import Formalization.ModelFree.QLearningHardMDPValues
import Formalization.ModelFree.QLearningLowerBoundTheorem
import Formalization.ModelFree.QLearningLowerBoundRescaledTheorem
import Formalization.ModelFree.QLearningStepSizeSource
import Formalization.ModelFree.TDStepSizeLate
import Formalization.Statements.Ch4
import Formalization.ModelFree.FiniteQ.Main
import Formalization.ModelFree.TDIterateBounds
import Formalization.ModelFree.TDSquareEnergy
import Formalization.ModelFree.TDSourceVarianceProxyUniversal
import Formalization.ModelFree.TDSourceAccuracyExactSamples
import Formalization.ModelFree.QLearningIterateBounds
import Formalization.ModelFree.QLearningStabilityInfinityNorm
import Formalization.ModelFree.QLearningRobustContraction
import Formalization.ModelFree.QLearningSourceTheoremClosure
import Formalization.ModelFree.AsyncQ.Main
import Formalization.ModelFree.MeanError
import Formalization.ModelFree.AsyncQ.MeanError
import Formalization.ModelFree.QLearningUnderestimation
import Formalization.ModelFree.QLearningRateFacts
import Formalization.ModelFree.QLearningSingleActionTD

/-! Proofs of the Chapter 4 statement index from the existing exports. -/
namespace StatisticalRL.Statements.Ch4
open StatisticalRL.TemporalDifference StatisticalRL.QLearning
universe u v

theorem Thm4_1_holds : Thm4_1 := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _hc₁le, hc₃, hsource⟩ :=
    tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants
  refine ⟨c₁, c₂, c₃, hc₂, horder, hc₃, ?_⟩
  intro State Action instState instAction M π η δ ε T hγhalf hγone hT
    hδ hδone hε hεmax hη V₀ h₀ hbudget
  have hεsource : ε ≤ M.effectiveHorizon := by
    simpa [DiscountedMDP.effectiveHorizon] using hεmax
  have hηsource : ∀ t, 1 ≤ t → t ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2) ≤ η t ∧
      η t ≤ 1 / (1 + c₂ * (1 - M.discount) * t / Real.log (T : ℝ) ^ 2) :=
    fun t ht htT ↦ hη t ht htT
  have h₀source : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon := by
    intro s
    constructor
    · exact (h₀ s).1
    · simpa [DiscountedMDP.effectiveHorizon] using (h₀ s).2
  have hresult := hsource State Action M π η δ ε T hγhalf hT
    hδ hδone hε hεsource hηsource V₀ h₀source hbudget
  simpa only [tdErrorValue, tdSourceSampledIterate] using hresult

theorem Lemma4_2_holds : Lemma4_2 := by
  intro State Action instS instA M π η samples V₀ T h₀ hη t ht
  have hused : ∀ k, k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
    fun k hk ↦ hη k (hk.trans ht)
  exact ⟨fun s ↦ tdIterate_bounds M π η samples V₀ h₀ t hused s,
    tdIterate_error_norm_le M π η samples V₀ h₀ t hused⟩

theorem Lemma4_4_holds : Lemma4_4 := by
  intro State Action instS instA M π η T V₀ h₀ hη k hk hkT
  exact tdSquaredIterateEnergy M π η T V₀ h₀ hη k hk hkT

theorem Lemma4_5_holds : Lemma4_5 := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _, hc₃, h⟩ :=
    tdSource_varianceProxy_exists_universal_constants
  exact ⟨c₁, c₂, c₃, hc₂, horder, hc₃, h⟩

theorem Lemma4_8_holds : Lemma4_8 := by
  intro State Action instS instA M η samples Q₀ t h₀ hη
  have hused : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
    fun k _ _ ↦ hη k
  exact ⟨fun s a ↦ qLearningIterate_bounds M η samples Q₀ h₀ t hused s a,
    fun s ↦ qLearningIterate_value_bounds M η samples Q₀ h₀ t hused s,
    qLearningIterate_optimalQ_error_norm_le M η samples Q₀ h₀ t hused⟩

theorem Lemma4_10_holds : Lemma4_10 := by
  constructor
  · intro State instS instN p γ ρ _hγnonneg hγ hρ value hspan
    exact qComparisonFacts_support_source p γ ρ hγ hρ value hspan
  · intro State Action instS instA M M' ρ hρ hr hγ hballs
    exact qComparisonFacts_stability_source M M' ρ hρ hr hγ hballs

theorem Lemma4_11_holds : Lemma4_11 := by
  intro State Action instS instA M ρ hρ
  dsimp only
  intro Q R
  have h := qRobustBellman_contracting M ρ (2 * ρ / (1 - M.discount)) hρ.le
  constructor
  · simpa [dist_eq_norm, DiscountedMDP.coe_discountConstant] using h.1.2.dist_le_mul Q R
  · simpa [dist_eq_norm, DiscountedMDP.coe_discountConstant] using h.2.2.dist_le_mul Q R

theorem Thm4_6_holds : Thm4_6 := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _, hc₃, h⟩ :=
    qLearning_exists_universal_constants_source_accuracy
  exact ⟨c₁, c₂, c₃, hc₂, horder, hc₃, h⟩

theorem Thm4_6_underestimation_holds : Thm4_6_underestimation :=
  qLearning_underestimation_exists_universal_constants

theorem Lemma4_3_corrected_holds : Lemma4_3_corrected := by
  intro γ c₁ c₂ T η hT hγ hγ1 hc₁ hc₂ hcprod hlarge hs t k htT hkt htime
  exact tdRateWeight_corrected_step_size γ c₁ c₂ T η hT hγ hγ1 hc₁ hc₂ hcprod hlarge hs
    t k htT hkt htime

theorem Lemma4_9_holds : Lemma4_9 := by
  intro γ c₁ c₂ T η hT hγ1 hc₁ hc₂ hs
  exact qSource_step_size_weights γ c₁ c₂ T η hT hγ1 hc₁ hc₂ hs

theorem Lemma4_14_holds : Lemma4_14 := by
  intro γ hγ hγ1
  exact qHardMDP_optimal_values γ hγ hγ1

theorem Thm4_7_restricted_holds : Thm4_7_restricted := qLb_thm47_constantRate

theorem Thm4_7_holds : Thm4_7 := qLb_thm47

theorem Thm4_7_case_i_holds : Thm4_7_case_i := qLb_thm47_rescaledLinear

theorem Lemma4_15_holds : Lemma4_15 := qLb_lemma415

theorem Thm4_13_corrected_holds : Thm4_13_corrected := by
  refine ⟨1 / 64, by norm_num, fun c₁ c₂ hc₂ hc₂₁ hc₁ ↦ ⟨8000 / c₂, by positivity, ?_⟩⟩
  intro State Action _ _ H E η δ ε T hT hδ hδ1 hε hε1 hη hbudget Q₀ hQ₀
  exact FiniteQLearning.finiteQLearning_sample_complexity c₁ c₂ hc₂ hc₂₁ hc₁ H E η δ ε T hT hδ
    hδ1 hε hε1 (fun k _ hk ↦ hη k hk) Q₀ hQ₀ hbudget

open Classical in
theorem Thm4_12_corrected_holds : Thm4_12_corrected := by
  obtain ⟨c₂, hc₂, h⟩ := AsyncQ.asyncQ_exists_c₂ 1 one_pos le_rfl
  refine ⟨1, one_pos, le_rfl, c₂, hc₂, ?_⟩
  intro S A _ _ M πb μ μmin tmix s₀ δ ε T hγ hst _ htmix hμmin _ hμ0 hT1 hT2 hδ hδ1 hε hε1 hbud
    Q₀ h₀
  exact h S A M πb μ μmin tmix s₀ δ ε T hγ hst htmix.1 hμmin hμ0 hT1 hT2 hδ hδ1 hε hε1 hbud Q₀ h₀

theorem Remark4_1_holds : Remark4_1 := tdSource_meanError_exists_universal_constants

theorem Remark4_2_holds : Remark4_2 := qLearning_meanError_exists_universal_constants

open Classical in
theorem Remark4_3_corrected_holds : Remark4_3_corrected :=
  AsyncQ.asyncQ_meanError_exists_constants

theorem Thm4_6_constantRate_holds : Thm4_6_constantRate := by
  intro c₁ c₂ c₃ γ ε δ S A T hc₂ hc₂₁ hc₃ _ hγ1 hε hδ hδ1 hS hA hT
  exact constantRate_schedule_and_bound c₁ c₂ c₃ γ ε δ S A T hc₂ hc₂₁ hc₃ hγ1 hε hδ hδ1 hS hA hT

theorem Thm4_7_iterationLowerBound_holds : Thm4_7_iterationLowerBound :=
  qLb_thm47_iterationLowerBound

theorem Remark4_5_holds : Remark4_5 := by
  refine ⟨fun γ hγ hγ1 η N t a ht ↦ ?_, ?_⟩
  · have hrow := qLbMDP_rowSpec γ (by linarith) hγ1
    refine ⟨fun W hW ↦ ?_, ?_⟩
    · exact qLb_integral_xi_adapted _ N γ η hrow t ht a W (fun n s s' h ↦ hW n s s' h)
    · exact qLb_integral_xi_adapted _ N γ η hrow t ht a
        (fun n s ↦ qLbSingleAuxIterate γ η a s n)
        (fun n s s' h ↦ qLbSingleAuxIterate_congr γ η a n s s' h)
  · obtain ⟨c, c₃, hc, hc₃, hmain⟩ := qLb_lemma415
    refine ⟨max c₃ 1, lt_max_of_lt_right one_pos, ?_⟩
    intro γ hγ hγ1 T η hT hηlow hηup p ρ τhat hτ hτmax t N htτ htN
    have hh : 0 < 1 - γ := by linarith
    have hg2 : 0 < (1 - γ) ^ 2 := by positivity
    have hT3 : c₃ / (1 - γ) ^ 2 ≤ T :=
      le_trans (div_le_div_of_nonneg_right (le_max_left _ _) hg2.le) hT
    have hT1 : 1 / (1 - γ) ^ 2 ≤ T :=
      le_trans (div_le_div_of_nonneg_right (le_max_right _ _) hg2.le) hT
    have hT16 : (16 : ℝ) ≤ T := by
      have hsm : (1 - γ) ^ 2 ≤ 1 / 16 := by nlinarith
      have : (16 : ℝ) ≤ 1 / (1 - γ) ^ 2 := by
        rw [le_div_iff₀ hg2]; linarith
      linarith
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hsq : 0 < Real.sqrt ((1 - γ) ^ 2 * T) := Real.sqrt_pos.mpr (by positivity)
    have hlb := (hmain γ hγ hγ1 T η hT3 hηlow hηup).2 τhat hτ hτmax t N htτ htN
    exact lt_of_lt_of_le (by positivity) hlb

theorem QLearning_singleAction_eq_TD_holds : QLearning_singleAction_eq_TD.{u, v} := by
  intro State Action _ _ _ M π a η Q₀
  exact ⟨fun samples t s ↦ qLearningIterate_singleAction M π a η samples Q₀ t s,
    fun T B ↦ qSampled_singleAction_event_eq M π a η T Q₀ B,
    fun s ↦ optimalQ_singleAction_eq_value M π a s⟩

end StatisticalRL.Statements.Ch4
