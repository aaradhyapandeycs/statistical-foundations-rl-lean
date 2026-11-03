import Formalization.ModelFree.QLearningChiFixedValueHistory

/-! Finite predictable-variance identity and actual
source-schedule budget for an arbitrary deterministic fixed value vector. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiVarianceStateMeasurable : MeasurableSpace State := ⊤
local instance qChiVarianceActionMeasurable : MeasurableSpace Action := ⊤

noncomputable def qChiFixedVarianceBudget (M : DiscountedMDP State Action) (v : State → ℝ)
    (c₂ : ℝ) (T : ℕ) (s : State) (a : Action) : ℝ :=
  M.discount^2 * qSourceLateCap M.discount c₂ T * qRowVariance M s a v

theorem qChiFixedRowVariance_nonneg (M : DiscountedMDP State Action) (v : State → ℝ)
    (s : State) (a : Action) : 0 ≤ qRowVariance M s a v := by
  rw [qRowVariance_eq_distribution]
  exact (M.transition s a).variance_nonneg _

/-- Inactive entries vanish identically, including every n>=T. -/
theorem qChiFixedFluctuation_inactive (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (T u n : ℕ) (s : State) (a : Action)
    (hn : ¬(n < T ∧ T/2 < n+1 ∧ n+1 ≤ u)) :
    qChiFixedFluctuationIncrement M v η T u s a n = 0 := by
  funext data
  simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, hn]

theorem qChiFixedFluctuation_inactive_condExp_sq (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (T u n : ℕ) (s : State) (a : Action)
    (hn : ¬(n < T ∧ T/2 < n+1 ∧ n+1 ≤ u)) :
    (qSamplingLaw M T)[(fun data ↦ (qChiFixedFluctuationIncrement M v η T u s a n data)^2) |
      priorIncrementSigma (qChiFixedFluctuationIncrement M v η T u s a) n]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  have hz := qChiFixedFluctuation_inactive M v η T u n s a hn
  have hf : (fun data : QSamples State Action T ↦
      (qChiFixedFluctuationIncrement M v η T u s a n data)^2) = 0 := by
    rw [hz]
    ext data
    simp
  rw [hf, condExp_zero]
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Exact fixed-terminal predictable variance as an almost-everywhere constant.
Active moments come from the actual row law; inactive terms are zero. -/
theorem qChiFixed_historyPredictableVariance_exact (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (T u : ℕ) (s : State) (a : Action) :
    historyPredictableVariance (qSamplingLaw M T) (qChiFixedFluctuationIncrement M v η T u s a) T
      =ᵐ[qSamplingLaw M T] fun _ ↦ M.discount^2 * qOptimalActiveWeightSquareSum η T u *
        qRowVariance M s a (v) := by
  classical
  have heach : ∀ t, ∀ᵐ data ∂qSamplingLaw M T,
      (qSamplingLaw M T)[(fun data ↦ (qChiFixedFluctuationIncrement M v η T u s a t data)^2) |
        priorIncrementSigma (qChiFixedFluctuationIncrement M v η T u s a) t] data =
      if t ∈ qActiveLayers T u then
        (M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (v)
      else 0 := by
    intro t
    by_cases ht : t ∈ qActiveLayers T u
    · have ht' := Finset.mem_filter.mp ht
      have hactive : t < T ∧ T/2 < t+1 ∧ t+1 ≤ u :=
        ⟨Finset.mem_range.mp ht'.1, ht'.2.1, ht'.2.2⟩
      simpa [ht] using qChiFixedFluctuation_condExp_natural_sq M v η T u t s a hactive
    · have hnot : ¬ (t < T ∧ T/2 < t+1 ∧ t+1 ≤ u) := by
        intro h
        apply ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2⟩
      simpa [ht] using qChiFixedFluctuation_inactive_condExp_sq M v η T u t s a hnot
  filter_upwards [ae_all_iff.mpr heach] with data hd
  unfold historyPredictableVariance qOptimalActiveWeightSquareSum
  simp_rw [hd]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range T).filter (fun t ↦ t ∈ qActiveLayers T u) = qActiveLayers T u := by
    ext t
    simp [qActiveLayers]
  rw [hfilter, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Source schedule gives a deterministic true-row predictable-variance cap. -/
theorem qChiFixed_historyPredictableVariance_le (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T u : ℕ) (hT : 2 ≤ T) (hu : u ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (s : State) (a : Action) :
    ∀ᵐ data ∂qSamplingLaw M T,
      historyPredictableVariance (qSamplingLaw M T) (qChiFixedFluctuationIncrement M v η T u s a) T data ≤
        qChiFixedVarianceBudget M v c₂ T s a := by
  have hw := qSourceLate_weight_squares_le M.discount c₁ c₂ T u η hT M.discount_lt_one hc₁ hc₂ hu hs
  rw [← qOptimalActiveWeightSquareSum_eq_source η T u hu] at hw
  have hv := qChiFixedRowVariance_nonneg M v s a
  filter_upwards [qChiFixed_historyPredictableVariance_exact M v η T u s a] with data hd
  rw [hd]
  unfold qChiFixedVarianceBudget
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (sq_nonneg M.discount)) hv


end StatisticalRL.QLearning
