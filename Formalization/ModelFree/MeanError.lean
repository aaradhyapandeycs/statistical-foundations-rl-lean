import Formalization.ModelFree.TDSourceAccuracyExactSamples
import Formalization.ModelFree.TDErrorCaps
import Formalization.ModelFree.QLearningSourceTheoremClosure
import Formalization.ModelFree.QLearningSynchronousSampling
import Formalization.ModelFree.AsyncQ.Main
import Formalization.MDP.InfiniteReturn
import Formalization.MDP.ForcedActionReturn

/-!
# Mean ℓ∞ estimation error from high-probability guarantees (Remarks 4.1–4.3)

Source: arXiv:2610.41903v1, `chapters/generative_model_model_free.tex`, Remark 4.1 (:226–239),
Remark 4.2 (:914–929) and Remark 4.3 (:2088–2090). Each remark takes `δ = ε(1−γ)/2` in the
corresponding high-probability theorem and splits the expectation over the good event, using the
crude bound `|error| ≤ 1/(1−γ)` off it: `E[max |error|] ≤ ε(1−δ) + δ/(1−γ) ≤ 2ε`. Remark 4.3 is
the corrected reading carrying the premises of `Thm4_12_corrected` (`docs/SOURCE-ISSUES.md#C34`).
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.MeanError

/-- Splitting an expectation over a high-probability event: a sup of bounded absolute errors that
is at most `ε` on an event of probability `≥ 1 − δ` and at most `B ≥ ε` everywhere has
expectation at most `ε(1−δ) + Bδ`. Integrability is part of the conclusion. -/
theorem integral_iSup_abs_le_of_highProb {Ω ι : Type*} [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] [Finite ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ι → ℝ) {G : Set Ω} {ε B δ : ℝ}
    (hB : ∀ ω i, |g ω i| ≤ B) (hεB : ε ≤ B)
    (hGsub : ∀ ω ∈ G, ∀ i, |g ω i| ≤ ε) (hG : 1 - δ ≤ μ.real G) :
    Integrable (fun ω ↦ ⨆ i, |g ω i|) μ ∧
      ∫ ω, (⨆ i, |g ω i|) ∂μ ≤ ε * (1 - δ) + B * δ := by
  set f : Ω → ℝ := fun ω ↦ ⨆ i, |g ω i| with hfdef
  have hbdd : ∀ ω, BddAbove (Set.range fun i ↦ |g ω i|) := fun ω ↦ Set.finite_range _ |>.bddAbove
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω ↦
    (abs_nonneg _).trans (le_ciSup (hbdd ω) (Classical.arbitrary ι))
  have hfB : ∀ ω, f ω ≤ B := fun ω ↦ ciSup_le (hB ω)
  have hfG : ∀ ω ∈ G, f ω ≤ ε := fun ω hω ↦ ciSup_le (hGsub ω hω)
  have hfm : Measurable f := Measurable.of_discrete
  have hint : Integrable f μ :=
    Integrable.mono' (integrable_const B) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hfB ω)
  refine ⟨hint, ?_⟩
  have hGm : MeasurableSet G := MeasurableSet.of_discrete
  have hind : Integrable (G.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hGm
  have hpt : ∀ ω, f ω ≤ B - (B - ε) * G.indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω, Pi.one_apply]
      have := hfG ω hω
      linarith
    · rw [Set.indicator_of_notMem hω]
      have := hfB ω
      linarith
  have hmono : ∫ ω, f ω ∂μ ≤ ∫ ω, (B - (B - ε) * G.indicator (1 : Ω → ℝ) ω) ∂μ :=
    integral_mono hint ((integrable_const B).sub (hind.const_mul (B - ε))) hpt
  have hrhs : ∫ ω, (B - (B - ε) * G.indicator (1 : Ω → ℝ) ω) ∂μ = B - (B - ε) * μ.real G := by
    rw [integral_sub (integrable_const B) (hind.const_mul (B - ε)), integral_const,
      integral_const_mul, integral_indicator_one hGm, probReal_univ, smul_eq_mul, one_mul]
  have hfin : B - (B - ε) * μ.real G ≤ ε * (1 - δ) + B * δ := by
    have := mul_le_mul_of_nonneg_left hG (sub_nonneg.mpr hεB)
    nlinarith
  change ∫ ω, f ω ∂μ ≤ _
  linarith

/-- The scalar closing step shared by Remarks 4.1–4.3: with `δ = ε(1−γ)/2`,
`0 < δ < 1` and `ε(1−δ) + δ/(1−γ) ≤ 2ε` whenever `0 < ε` and `ε(1−γ) ≤ 1`. -/
theorem meanError_scalar {γ ε : ℝ} (hγ1 : γ < 1) (hε : 0 < ε) (hεγ : ε * (1 - γ) ≤ 1) :
    0 < ε * (1 - γ) / 2 ∧ ε * (1 - γ) / 2 < 1 ∧
      ε * (1 - ε * (1 - γ) / 2) + 1 / (1 - γ) * (ε * (1 - γ) / 2) ≤ 2 * ε := by
  have hh : 0 < 1 - γ := by linarith
  have hδ0 : 0 < ε * (1 - γ) / 2 := by positivity
  refine ⟨hδ0, by linarith, ?_⟩
  have e : 1 / (1 - γ) * (ε * (1 - γ) / 2) = ε / 2 := by field_simp
  rw [e]
  have := mul_pos hε hδ0
  nlinarith

end StatisticalRL.MeanError

namespace StatisticalRL.TemporalDifference
open StatisticalRL.MeanError

local instance meanErrorStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Remark 4.1 (`chapters/generative_model_model_free.tex:226–239`) from the Theorem 4.1 accuracy
statement for a FIXED schedule pair `c₁ ≥ c₂ > 0`, whichever constants it holds for. -/
theorem tdSource_meanError_of_accuracy {State : Type*} {Action : Type*} [Fintype State]
    [Fintype Action] (c₁ c₂ c₃ : ℝ) (hc₂ : 0 < c₂) (horder : c₂ ≤ c₁)
    (hsource : ∀ (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
      1 - δ ≤ (tdSourceSamplingLaw M π T).real
        {data | ∀ s : State,
          |tdSourceSampledIterate M π η T V₀ data s -
            M.trajectoryExpectedValue π s| ≤ ε}) :
    ∀ (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount → M.discount < 1 → 2 ≤ T →
      0 < ε → ε ≤ 1 / (1 - M.discount) →
      (∀ t, 1 ≤ t → t ≤ T →
        1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2) ≤ η t ∧
        η t ≤ 1 / (1 + c₂ * (1 - M.discount) * t / Real.log (T : ℝ) ^ 2)) →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ 1 / (1 - M.discount)) →
      c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (2 * (Fintype.card State : ℝ) * T / (ε * (1 - M.discount))) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
      let δ := ε * (1 - M.discount) / 2
      let err := fun data ↦ ⨆ s : State,
        |tdSourceSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s|
      0 < δ ∧ δ < 1 ∧
      Integrable err (tdSourceSamplingLaw M π T) ∧
      ∫ data, err data ∂(tdSourceSamplingLaw M π T) ≤
        ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
      ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε := by
  intro M π η ε T hγhalf hγone hT hε hεmax hη V₀ h₀ hbudget δ err
  have hh : 0 < 1 - M.discount := by linarith
  have hεγ : ε * (1 - M.discount) ≤ 1 := by
    have := (le_div_iff₀ hh).1 hεmax
    linarith
  obtain ⟨hδ0, hδ1, hscalar⟩ := meanError_scalar hγone hε hεγ
  have hεsource : ε ≤ M.effectiveHorizon := by
    simpa [DiscountedMDP.effectiveHorizon] using hεmax
  have h₀source : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon := fun s ↦
    ⟨(h₀ s).1, by simpa [DiscountedMDP.effectiveHorizon] using (h₀ s).2⟩
  have hlogarg : (Fintype.card State : ℝ) * T / δ =
      2 * (Fintype.card State : ℝ) * T / (ε * (1 - M.discount)) := by
    simp only [δ]
    rw [div_div_eq_mul_div]
    ring
  have hbudget' : c₃ * Real.log (T : ℝ) ^ 3 * Real.log ((Fintype.card State : ℝ) * T / δ) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) := by
    rw [hlogarg]; exact hbudget
  have hp := hsource M π η δ ε T hγhalf hT hδ0 hδ1 hε hεsource hη V₀ h₀source
    hbudget'
  -- the crude pathwise bound
  have hc₁ : 0 < c₁ := lt_of_lt_of_le hc₂ horder
  have hηunit : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi hiT
    obtain ⟨hlo, hhi⟩ := hη i hi hiT
    have hx : 0 ≤ c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hc₁.le hh.le) (Nat.cast_nonneg _)) (sq_nonneg _)
    have hy : 0 ≤ c₂ * (1 - M.discount) * i / Real.log (T : ℝ) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hc₂.le hh.le) (Nat.cast_nonneg _)) (sq_nonneg _)
    refine ⟨le_trans (div_nonneg zero_le_one (by linarith)) hlo, hhi.trans ?_⟩
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hcrude : ∀ data s, |tdSourceSampledIterate M π η T V₀ data s -
      M.trajectoryExpectedValue π s| ≤ 1 / (1 - M.discount) := by
    intro data s
    have h1 := tdIterate_bounds_positive_rates M π η (tdSourceSamplesExtend M T data) V₀
      h₀source T hηunit s
    have h2 := M.trajectoryExpectedValue_bounds π s
    simp only [DiscountedMDP.effectiveHorizon] at h1
    simp only [tdSourceSampledIterate]
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  haveI : Nonempty State := M.state_nonempty
  haveI : IsProbabilityMeasure (tdSourceSamplingLaw M π T) := by
    unfold tdSourceSamplingLaw ModelBasedPolicyEvaluation.samplingLaw
    infer_instance
  obtain ⟨hI, hE⟩ := integral_iSup_abs_le_of_highProb (tdSourceSamplingLaw M π T)
    (fun data s ↦ tdSourceSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s)
    hcrude hεmax (fun _ hω ↦ hω) hp
  exact ⟨hδ0, hδ1, hI, hE, hscalar⟩


/-- Remark 4.1 (`chapters/generative_model_model_free.tex:226–239`): mean ℓ∞ TD estimation error
`≤ ε(1−δ) + δ/(1−γ) ≤ 2ε` with `δ = ε(1−γ)/2`, with the constants of Theorem 4.1. -/
theorem tdSource_meanError_exists_universal_constants :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount → M.discount < 1 → 2 ≤ T →
      0 < ε → ε ≤ 1 / (1 - M.discount) →
      (∀ t, 1 ≤ t → t ≤ T →
        1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2) ≤ η t ∧
        η t ≤ 1 / (1 + c₂ * (1 - M.discount) * t / Real.log (T : ℝ) ^ 2)) →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ 1 / (1 - M.discount)) →
      c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (2 * (Fintype.card State : ℝ) * T / (ε * (1 - M.discount))) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
      let δ := ε * (1 - M.discount) / 2
      let err := fun data ↦ ⨆ s : State,
        |tdSourceSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s|
      0 < δ ∧ δ < 1 ∧
      Integrable err (tdSourceSamplingLaw M π T) ∧
      ∫ data, err data ∂(tdSourceSamplingLaw M π T) ≤
        ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
      ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _hc₁le, hc₃, hsource⟩ :=
    tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants
  refine ⟨c₁, c₂, c₃, hc₂, horder, hc₃, ?_⟩
  intro State Action _ _
  exact tdSource_meanError_of_accuracy c₁ c₂ c₃ hc₂ horder
    (fun M π η δ ε T ↦ hsource State Action M π η δ ε T)

end StatisticalRL.TemporalDifference

namespace StatisticalRL.QLearning
open StatisticalRL.MeanError

local instance meanErrorQStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Remark 4.2 (`chapters/generative_model_model_free.tex:914–929`) from the Theorem 4.6 accuracy
statement for a FIXED schedule pair `c₁ ≥ c₂ > 0`, whichever constants it holds for. -/
theorem qLearning_meanError_of_accuracy {State : Type*} {Action : Type*} [Fintype State]
    [Fintype Action] (c₁ c₂ c₃ : ℝ) (hc₂ : 0 < c₂) (horder : c₂ ≤ c₁)
    (hsource : ∀ (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      qSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (Q₀ : State → Action → ℝ),
      (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ) ^ 4 * Real.log
        ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) /
          ((1 - M.discount) ^ 4 * ε ^ 2) ≤ T →
      1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
        |qSampledIterate M η T Q₀ data s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε}) :
    ∀ (M : DiscountedMDP State Action) (η : ℕ → ℝ) (ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
      0 < ε → ε ≤ M.effectiveHorizon →
      (∀ k, k ≤ T →
        1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
        η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
      ∀ (Q₀ : State → Action → ℝ),
      (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ)^4 * Real.log
        (2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T /
          (ε * (1 - M.discount))) /
        ((1-M.discount)^4*ε^2) ≤ T →
      let δ := ε * (1 - M.discount) / 2
      let err := fun data ↦ ⨆ p : State × Action,
        |qSampledIterate M η T Q₀ data p.1 p.2 -
          M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2|
      0 < δ ∧ δ < 1 ∧
      Integrable err (qSamplingLaw M T) ∧
      ∫ data, err data ∂(qSamplingLaw M T) ≤ ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
      ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε := by
  intro M η ε T hγhalf hA hT hε hεmax hη Q₀ h₀ hbudget δ err
  have hγone := M.discount_lt_one
  have hh : 0 < 1 - M.discount := by linarith
  have hεmax' : ε ≤ 1 / (1 - M.discount) := by
    simpa [DiscountedMDP.effectiveHorizon] using hεmax
  have hεγ : ε * (1 - M.discount) ≤ 1 := by
    have := (le_div_iff₀ hh).1 hεmax'
    linarith
  obtain ⟨hδ0, hδ1, hscalar⟩ := meanError_scalar hγone hε hεγ
  have hlogarg : (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ =
      2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T /
        (ε * (1 - M.discount)) := by
    simp only [δ]
    rw [div_div_eq_mul_div]
    ring
  have hbudget' : c₃ * Real.log (T : ℝ)^4 * Real.log
      ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) /
      ((1-M.discount)^4*ε^2) ≤ T := by
    rw [hlogarg]; exact hbudget
  have hp := hsource M η δ ε T hγhalf hA hT hδ0 hδ1 hε hεmax hη Q₀ h₀ hbudget'
  have hc₁ : 0 < c₁ := lt_of_lt_of_le hc₂ horder
  have hηunit : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1 := by
    intro k _ hkT
    obtain ⟨hlo, hhi⟩ := hη k hkT
    have hx : 0 ≤ c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3 := by
      apply div_nonneg (mul_nonneg (mul_nonneg hc₁.le hh.le) (Nat.cast_nonneg _))
      have : 0 ≤ Real.log (T : ℝ) := Real.log_natCast_nonneg T
      positivity
    have hy : 0 ≤ c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3 := by
      apply div_nonneg (mul_nonneg (mul_nonneg hc₂.le hh.le) (Nat.cast_nonneg _))
      have : 0 ≤ Real.log (T : ℝ) := Real.log_natCast_nonneg T
      positivity
    refine ⟨le_trans (div_nonneg zero_le_one (by linarith)) hlo, hhi.trans ?_⟩
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hcrude : ∀ data (p : State × Action), |qSampledIterate M η T Q₀ data p.1 p.2 -
      M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2| ≤ 1 / (1 - M.discount) := by
    intro data p
    have hn := qLearningIterate_optimalQ_error_norm_le M η (qSamplesExtend M T data) Q₀ h₀ T
      hηunit
    have h1 : ‖(qLearningIterate M η (qSamplesExtend M T data) Q₀ T -
        M.trajectoryExpectedQ M.optimalGreedyPolicy) p.1 p.2‖ ≤
        ‖qLearningIterate M η (qSamplesExtend M T data) Q₀ T -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖ :=
      (norm_le_pi_norm _ p.2).trans (norm_le_pi_norm _ p.1)
    rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply] at h1
    simpa [qSampledIterate, DiscountedMDP.effectiveHorizon] using h1.trans hn
  haveI : Nonempty State := M.state_nonempty
  haveI : Nonempty Action := M.action_nonempty
  obtain ⟨hI, hE⟩ := integral_iSup_abs_le_of_highProb (qSamplingLaw M T)
    (G := {data | ∀ s a, |qSampledIterate M η T Q₀ data s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε})
    (fun data (p : State × Action) ↦ qSampledIterate M η T Q₀ data p.1 p.2 -
      M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2)
    hcrude hεmax' (fun _ hω p ↦ hω p.1 p.2) hp
  exact ⟨hδ0, hδ1, hI, hE, hscalar⟩


/-- Remark 4.2 (`chapters/generative_model_model_free.tex:914–929`): mean ℓ∞ synchronous
Q-learning error `≤ ε(1−δ) + δ/(1−γ) ≤ 2ε` with `δ = ε(1−γ)/2`, with the constants of
Theorem 4.6. -/
theorem qLearning_meanError_exists_universal_constants :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (η : ℕ → ℝ) (ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
      0 < ε → ε ≤ M.effectiveHorizon →
      (∀ k, k ≤ T →
        1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
        η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
      ∀ (Q₀ : State → Action → ℝ),
      (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ)^4 * Real.log
        (2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T /
          (ε * (1 - M.discount))) /
        ((1-M.discount)^4*ε^2) ≤ T →
      let δ := ε * (1 - M.discount) / 2
      let err := fun data ↦ ⨆ p : State × Action,
        |qSampledIterate M η T Q₀ data p.1 p.2 -
          M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2|
      0 < δ ∧ δ < 1 ∧
      Integrable err (qSamplingLaw M T) ∧
      ∫ data, err data ∂(qSamplingLaw M T) ≤ ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
      ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _hc₁le, hc₃, hsource⟩ :=
    qLearning_exists_universal_constants_source_accuracy
  refine ⟨c₁, c₂, c₃, hc₂, horder, hc₃, ?_⟩
  intro State Action _ _
  exact qLearning_meanError_of_accuracy c₁ c₂ c₃ hc₂ horder
    (fun M η δ ε T ↦ hsource State Action M η δ ε T)

end StatisticalRL.QLearning
