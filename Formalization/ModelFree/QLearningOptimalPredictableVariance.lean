import Formalization.ModelFree.QLearningSourceLateCaps
import Formalization.ModelFree.QLearningSourceReindex
import Formalization.Probability.FreedmanNaturalHistory

/-! actual fixed-terminal predictable variance budget. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptBudgetStateMeasurable : MeasurableSpace State := ⊤
local instance qOptBudgetActionMeasurable : MeasurableSpace Action := ⊤

/-- Deterministic source variance budget before replacing true variance by H². -/
noncomputable def qOptimalVarianceBudget (M : DiscountedMDP State Action)
    (c₂ : ℝ) (T : ℕ) (s : State) (a : Action) : ℝ :=
  M.discount^2 * qSourceLateCap M.discount c₂ T *
    qRowVariance M s a (qTrueOptimalValue M)

/-- Inactive source increments have zero conditional square under their own
natural history, including all t≥T. -/
theorem qOptimalFluctuation_inactive_condExp_sq (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T u t : ℕ) (s : State) (a : Action)
    (h : ¬ (t < T ∧ T/2 < t+1 ∧ t+1 ≤ u)) :
    (qSamplingLaw M T)[(fun data ↦ (qOptimalFluctuationIncrement M η T u s a t data)^2) |
      priorIncrementSigma (qOptimalFluctuationIncrement M η T u s a) t]
        =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  have hz := qOptimalFluctuation_inactive M η T u t s a h
  have hf : (fun data : QSamples State Action T ↦ (qOptimalFluctuationIncrement M η T u s a t data)^2) = 0 := by
    rw [hz]
    ext data
    simp
  rw [hf, condExp_zero]
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- A deterministic late-weight sum appearing in the exact predictable budget. -/
noncomputable def qOptimalActiveWeightSquareSum (η : ℕ → ℝ) (T u : ℕ) : ℝ :=
  ∑ t ∈ qActiveLayers T u, (qPositiveWeight η u (t+1))^2

/-- Reindex actual active samples by the source's positive update indices. -/
theorem qOptimalActiveWeightSquareSum_eq_source (η : ℕ → ℝ) (T u : ℕ) (hu : u ≤ T) :
    qOptimalActiveWeightSquareSum η T u =
      ∑ i ∈ Finset.Icc (T/2+1) u, (qPositiveWeight η u i)^2 := by
  classical
  unfold qOptimalActiveWeightSquareSum
  rw [Finset.sum_subtype (qActiveLayers T u) (fun _ ↦ Iff.rfl),
    Finset.sum_subtype (Finset.Icc (T/2+1) u) (fun _ ↦ Iff.rfl)]
  apply Fintype.sum_equiv (qActiveLayerEquiv T u hu)
  intro t
  rfl

/-- Actual row-variance definition agrees with the finite-distribution variance. -/
theorem qRowVariance_eq_distribution (M : DiscountedMDP State Action) (s : State) (a : Action)
    (v : State → ℝ) : qRowVariance M s a v = (M.transition s a).variance v := by
  rw [FiniteDistribution.variance_eq_expectation_centered_sq]
  rfl

/-- The variance of the actual transition row is nonnegative. -/
theorem qOptimalRowVariance_nonneg (M : DiscountedMDP State Action) (s : State) (a : Action) :
    0 ≤ qRowVariance M s a (qTrueOptimalValue M) := by
  rw [qRowVariance_eq_distribution]
  exact (M.transition s a).variance_nonneg _

/-- Exact fixed-terminal predictable variance as an almost-everywhere constant.
Active moments come from the actual row law; inactive terms are zero. -/
theorem qOptimal_historyPredictableVariance_exact (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T u : ℕ) (s : State) (a : Action) :
    historyPredictableVariance (qSamplingLaw M T) (qOptimalFluctuationIncrement M η T u s a) T
      =ᵐ[qSamplingLaw M T] fun _ ↦ M.discount^2 * qOptimalActiveWeightSquareSum η T u *
        qRowVariance M s a (qTrueOptimalValue M) := by
  classical
  have heach : ∀ t, ∀ᵐ data ∂qSamplingLaw M T,
      (qSamplingLaw M T)[(fun data ↦ (qOptimalFluctuationIncrement M η T u s a t data)^2) |
        priorIncrementSigma (qOptimalFluctuationIncrement M η T u s a) t] data =
      if t ∈ qActiveLayers T u then
        (M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (qTrueOptimalValue M)
      else 0 := by
    intro t
    by_cases ht : t ∈ qActiveLayers T u
    · have ht' := Finset.mem_filter.mp ht
      have hactive : t < T ∧ T/2 < t+1 ∧ t+1 ≤ u :=
        ⟨Finset.mem_range.mp ht'.1, ht'.2.1, ht'.2.2⟩
      simpa [ht] using qOptimalFluctuation_condExp_natural_sq M η T u t s a hactive
    · have hnot : ¬ (t < T ∧ T/2 < t+1 ∧ t+1 ≤ u) := by
        intro h
        apply ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2⟩
      simpa [ht] using qOptimalFluctuation_inactive_condExp_sq M η T u t s a hnot
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
theorem qOptimal_historyPredictableVariance_le (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T u : ℕ) (hT : 2 ≤ T) (hu : u ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (s : State) (a : Action) :
    ∀ᵐ data ∂qSamplingLaw M T,
      historyPredictableVariance (qSamplingLaw M T) (qOptimalFluctuationIncrement M η T u s a) T data ≤
        qOptimalVarianceBudget M c₂ T s a := by
  have hw := qSourceLate_weight_squares_le M.discount c₁ c₂ T u η hT M.discount_lt_one hc₁ hc₂ hu hs
  rw [← qOptimalActiveWeightSquareSum_eq_source η T u hu] at hw
  have hv := qOptimalRowVariance_nonneg M s a
  filter_upwards [qOptimal_historyPredictableVariance_exact M η T u s a] with data hd
  rw [hd]
  unfold qOptimalVarianceBudget
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (sq_nonneg M.discount)) hv

/- The preceding candidate proof consumes the source schedule through
qSourceLate_weight_squares_le, whose proof uses qLate_weight_squares_le and
qPositiveWeight_late_sum_le_one derived from the telescope; it does not assume
an extra squared-weight bound. Active and inactive moments are combined over
exactly range T, and the active/source reindex uses u≤T. The proof and all
imports still require focused compilation and independent source review. -/
end StatisticalRL.QLearning
