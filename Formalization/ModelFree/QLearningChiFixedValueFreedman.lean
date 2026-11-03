import Formalization.ModelFree.QLearningChiFixedValueVariance

/-! actual-law generic deterministic-value Freedman
bound, deriving both budgets from source schedule and centered span. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiFreedmanStateMeasurable : MeasurableSpace State := ⊤
local instance qChiFreedmanActionMeasurable : MeasurableSpace Action := ⊤

noncomputable def qChiFixedFluctuationSum (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (T u : ℕ) (s : State) (a : Action) (data : QSamples State Action T) : ℝ :=
  ∑ n ∈ Finset.range T, qChiFixedFluctuationIncrement M v η T u s a n data

theorem qChiFixedFluctuation_freedman (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (c₁ c₂ : ℝ) (T u : ℕ) (hT : 2 ≤ T) (hu : u ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (hspan : ∀ x y, |v x - v y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (qSamplingLaw M T).real {data |
      |qChiFixedFluctuationSum M v η T u s a data| ≤
        Real.sqrt (8 * max
          (historyPredictableVariance (qSamplingLaw M T) (qChiFixedFluctuationIncrement M v η T u s a) T data)
          (qChiFixedVarianceBudget M v c₂ T s a / (2 : ℝ)^K) * Real.log (2*K/δ)) +
        (4/3) * (M.discount * qSourceLateCap M.discount c₂ T * M.effectiveHorizon) * Real.log (2*K/δ)} := by
  let X := qChiFixedFluctuationIncrement M v η T u s a
  let B := M.discount * qSourceLateCap M.discount c₂ T * M.effectiveHorizon
  let V := qChiFixedVarianceBudget M v c₂ T s a
  have hcap : 0 ≤ qSourceLateCap M.discount c₂ T := by
    unfold qSourceLateCap
    have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
    have hgap : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
    positivity
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg M.discount_nonneg hcap) M.effectiveHorizon_nonneg
  have hV : 0 ≤ V := mul_nonneg (mul_nonneg (sq_nonneg M.discount) hcap) (qChiFixedRowVariance_nonneg M v s a)
  have hX : ∀ n, Measurable (X n) := fun n ↦
    ((qChiFixedFluctuation_strong_nextPast M v η T u n s a).mono (qPastSigma_le T (n+1))).measurable
  have hb : ∀ n, ∀ᵐ data ∂qSamplingLaw M T, |X n data| ≤ B := fun n ↦
    Filter.Eventually.of_forall (qChiFixedFluctuation_source_abs_le M v η c₁ c₂ T u hT hu hc₁ hc₂ hs hspan s a n)
  have hz : ∀ n, (qSamplingLaw M T)[X n | priorIncrementSigma X n] =ᵐ[qSamplingLaw M T] fun _ ↦ 0 :=
    fun n ↦ qChiFixedFluctuation_condExp_natural_zero M v η T u n s a
  have hvar : ∀ᵐ data ∂qSamplingLaw M T, historyPredictableVariance (qSamplingLaw M T) X T data ≤ V :=
    qChiFixed_historyPredictableVariance_le M v η c₁ c₂ T u hT hu hc₁ hc₂ hs s a
  have h := freedman_natural_history (qSamplingLaw M T) X hX B V hB hV hb hz T K hK hvar δ hδ hδ1
  have heq : ∀ data, incrementSum X T data = qChiFixedFluctuationSum M v η T u s a data := by
    intro data
    rfl
  simpa [X, B, V, heq] using h

end StatisticalRL.QLearning
