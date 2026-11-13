import Formalization.ModelFree.MeanError
import Formalization.ModelFree.TDSourceScheduleGeneral
import Formalization.ModelFree.TDSourceVarianceProxyLemma
import Formalization.ModelFree.QLearningConditionalUniversalConstants
import Formalization.ModelFree.QLearningSourceTheoremClosure

/-!
Lemma 4.5 and Remarks 4.1 and 4.2 (`chapters/generative_model_model_free.tex:727–743, 226–239,
914–929`) for EVERY schedule pair `0 < c₂ ≤ c₁ ≤ c₀` (threshold form), not only the single pair
used by the earlier exports. Only the budget constant `c₃` (depending on `c₁`, `c₂`) is
re-chosen; the component theorems already take the schedule constants as arguments.
-/

open MeasureTheory
namespace StatisticalRL.TemporalDifference

local instance scheduleGeneralRemarksStateMeasurable (State : Type*) :
    MeasurableSpace State := ⊤

/-- Source Lemma 4.5 (variance proxy bounds at an eligible terminal) for every schedule pair
`0 < c₂ ≤ c₁`, `c₁ c₂ ≤ 1/8`: the budget constant `c₃ = max(384, 1/(c₁ log² 2))` depends only on
`c₁`. -/
theorem tdSource_varianceProxy_exists_c₃ (c₁ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hcprod : c₁ * c₂ ≤ 1 / 8) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T t : ℕ),
      1/2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ)^3 *
        Real.log ((Fintype.card State : ℝ)*T/δ) /
          ((1-M.discount)^3*ε^2) ≤ T →
      t ≤ T → tdSourceEligibleTerminal T c₂ t →
      1-δ/(2*T) ≤ (tdSamplingLaw M π T).real
        {data |
          ‖tdSourceFixedTerminalProxyVector M π η T t V₀
            (tdSourceBarEta M.discount T) data‖ ≤
              16*tdSourceBarEta M.discount T*M.effectiveHorizon^2 ∧
          ‖fun s => tdTerminalVarianceSum M π η T t V₀ s data‖ ≤
            33*Real.log (T : ℝ)^3/((1-M.discount)^3*T)} := by
  have hc₁ : 0 < c₁ := hc₂.trans_le hc₂₁
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2sq : 0 < c₁ * Real.log 2 ^ 2 := by positivity
  let c₃ : ℝ := max 384 (1 / (c₁ * Real.log 2 ^ 2))
  have hc₃low : 384 ≤ c₃ := le_max_left _ _
  have hconst : 1 ≤ c₁ * c₃ * Real.log 2 ^ 2 := by
    have h : 1 / (c₁ * Real.log 2 ^ 2) ≤ c₃ := le_max_right _ _
    have := (div_le_iff₀ hlog2sq).mp h
    nlinarith [this]
  refine ⟨c₃, by linarith, ?_⟩
  intro State Action _ _ M π η δ ε T t hγ hT hδ hδ1 hε hεmax hs V₀ h₀ hbudget ht helig
  exact tdSource_varianceProxy_both_of_budget M π η T t hT c₁ c₂ c₃ ε δ hc₁ hc₂ hc₃low hcprod
    hconst hγ hδ hδ1 hε hεmax hbudget hs V₀ h₀ ht helig

/-- Remark 4.1 (`chapters/generative_model_model_free.tex:226–239`) for every schedule pair
`0 < c₂ ≤ c₁ ≤ 1/4`: the mean ℓ∞ error bound with the budget constant of the generalised
Theorem 4.1 (`tdSource_policyEvaluation_exactSamples_accuracy_exists_c₃`). -/
theorem tdSource_meanError_exists_c₃ (c₁ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hc₁ : c₁ ≤ 1 / 4) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
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
  obtain ⟨c₃, hc₃, hsource⟩ := tdSource_policyEvaluation_exactSamples_accuracy_exists_c₃ c₁ c₂
    hc₂ hc₂₁ (by nlinarith)
  refine ⟨c₃, hc₃, ?_⟩
  intro State Action _ _
  exact tdSource_meanError_of_accuracy c₁ c₂ c₃ hc₂ hc₂₁
    (fun M π η δ ε T ↦ hsource State Action M π η δ ε T)

end StatisticalRL.TemporalDifference

namespace StatisticalRL.QLearning

/-- Theorem 4.6 accuracy statement (synchronous Q-learning) for every schedule pair
`0 < c₂ ≤ c₁ ≤ 1`, with `c₃` depending only on `c₂` (`qFinal_exists_universal_budget_constant`). -/
theorem qLearning_source_accuracy_exists_c₃ (c₁ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hc₁ : c₁ ≤ 1) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
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
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε} := by
  obtain ⟨c₃, hc₃, he, hs, hd⟩ := qFinal_exists_universal_budget_constant c₂ hc₂
  refine ⟨c₃, hc₃, ?_⟩
  intro State Action instState instAction M η δ ε T hγhalf hA hT hδ hδ1 hε hεmax hschedule Q₀
    h₀ hbudget
  have hρ : 0 ≤ qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T := by
    have hηbar := qChiSourceRateEnvelope_pos M.discount c₂ T M.discount_lt_one hc₂ hT
    exact (qChiSourceRadius_pos _ δ _ _ T hηbar hδ hδ1
      (Fintype.card_pos_iff.mpr M.state_nonempty)
      (Fintype.card_pos_iff.mpr M.action_nonempty) hT).le
  exact qLearning_conditional_source_accuracy M η c₁ c₂ c₃ δ ε T hγhalf (hc₂.trans_le hc₂₁)
    hc₁ hc₂ hc₃ he hs hd hT hδ hδ1 hε hεmax hschedule Q₀ h₀ hbudget
    (qSource_robust_comparator_closeness_from_stopped_law M _ hρ)

/-- Remark 4.2 (`chapters/generative_model_model_free.tex:914–929`) for every schedule pair
`0 < c₂ ≤ c₁ ≤ 1`. -/
theorem qLearning_meanError_exists_c₃ (c₁ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hc₁ : c₁ ≤ 1) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
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
  obtain ⟨c₃, hc₃, hsource⟩ := qLearning_source_accuracy_exists_c₃ c₁ c₂ hc₂ hc₂₁ hc₁
  refine ⟨c₃, hc₃, ?_⟩
  intro State Action _ _
  exact qLearning_meanError_of_accuracy c₁ c₂ c₃ hc₂ hc₂₁
    (fun M η δ ε T ↦ hsource State Action M η δ ε T)

end StatisticalRL.QLearning
