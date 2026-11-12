import Formalization.ModelFree.QLearningChiStochasticInterface
import Formalization.ModelFree.QLearningConditionalPullout

/-! Actual fresh-row moments for an arbitrary fixed,
deterministic value vector. The value has no sample-data argument. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiFixedMomentStateMeasurable : MeasurableSpace State := ⊤
local instance qChiFixedMomentActionMeasurable : MeasurableSpace Action := ⊤

noncomputable abbrev qChiFixedFluctuationIncrement (M : DiscountedMDP State Action)
    (v : State → ℝ) (η : ℕ → ℝ) (T u : ℕ) (s : State) (a : Action) (n : ℕ) :
    QSamples State Action T → ℝ := qChiFixedValueIncrement M η T u v s a n

/-- The one-row fixed-value centered draw, before the deterministic source weight. -/
noncomputable def qChiFixedCenteredDraw (M : DiscountedMDP State Action) (v : State → ℝ) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) (data : QSamples State Action T) : ℝ :=
  v (data ((s,a), ⟨t,ht⟩)) -
    (M.transition s a).expectation (v)

/-- Conditional mean of the actual fixed deterministic-value centered draw is zero. -/
theorem qChiFixedCenteredDraw_condExp_zero (M : DiscountedMDP State Action) (v : State → ℝ) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) :
    (qSamplingLaw M T)[qChiFixedCenteredDraw M v T t ht s a | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  classical
  let c : State → QSamples State Action T → ℝ := fun x _ ↦ v x
  have heq : (fun data : QSamples State Action T ↦ v
      (data ((s,a), ⟨t,ht⟩))) = ∑ x, c x * qFreshIndicator T t ht s a x := by
    funext data
    simp [c, qFreshIndicator, Finset.sum_apply]
  have hs := qFresh_predictable_sum_condExp M T t ht s a c (fun _ ↦ stronglyMeasurable_const)
  have hmean : (qSamplingLaw M T)[(fun data ↦ v
      (data ((s,a), ⟨t,ht⟩))) | qPastSigma T t] =ᵐ[qSamplingLaw M T]
      fun _ ↦ (M.transition s a).expectation (v) := by
    rw [heq]
    filter_upwards [hs] with data hd
    simpa [c, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd
  have hsub := condExp_sub (qSampling_integrable M T (fun data ↦ v
      (data ((s,a), ⟨t,ht⟩)))) (qSampling_integrable M T (fun _ ↦
      (M.transition s a).expectation (v))) (qPastSigma T t)
  have hc := condExp_const (μ := qSamplingLaw M T) (qPastSigma_le T t)
      ((M.transition s a).expectation (v))
  change (qSamplingLaw M T)[(fun data ↦ v (data ((s,a), ⟨t,ht⟩))) -
    (fun _ ↦ (M.transition s a).expectation (v)) | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0
  filter_upwards [hsub, hmean] with data hd hm
  rw [hc] at hd
  simp only [Pi.sub_apply, hm, sub_self] at hd
  exact hd

/-- The fixed deterministic-value squared draw has exactly its true-row conditional variance. -/
theorem qChiFixedCenteredDraw_condExp_sq (M : DiscountedMDP State Action) (v : State → ℝ) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) :
    (qSamplingLaw M T)[(fun data ↦ (qChiFixedCenteredDraw M v T t ht s a data)^2) | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ qRowVariance M s a (v) := by
  classical
  let c : State → QSamples State Action T → ℝ := fun x _ ↦
    (v x - (M.transition s a).expectation (v))^2
  have heq : (fun data : QSamples State Action T ↦ (qChiFixedCenteredDraw M v T t ht s a data)^2) =
      ∑ x, c x * qFreshIndicator T t ht s a x := by
    funext data
    simp [c, qChiFixedCenteredDraw, qFreshIndicator, Finset.sum_apply]
  rw [heq]
  have h := qFresh_predictable_sum_condExp M T t ht s a c (fun _ ↦ stronglyMeasurable_const)
  filter_upwards [h] with data hd
  simpa [c, qRowVariance, qRowMean, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd

/-- Weighted source fluctuation is conditionally centered, including inactive layers. -/
theorem qChiFixedFluctuation_condExp_zero (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    (qSamplingLaw M T)[qChiFixedFluctuationIncrement M v η T u s a t | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  classical
  by_cases h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u
  · let w := M.discount * qPositiveWeight η u (t+1)
    have heq : qChiFixedFluctuationIncrement M v η T u s a t =
        w • qChiFixedCenteredDraw M v T t h.1 s a := by
      funext data
      simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, h, qChiFixedCenteredDraw, w, smul_eq_mul]
    rw [heq]
    have hs := condExp_smul (μ := qSamplingLaw M T) (m := qPastSigma T t)
      w (qChiFixedCenteredDraw M v T t h.1 s a)
    have hz := qChiFixedCenteredDraw_condExp_zero M v T t h.1 s a
    filter_upwards [hs, hz] with data hd hz'
    simpa [Pi.smul_apply, smul_eq_mul, hz'] using hd
  · have hz : qChiFixedFluctuationIncrement M v η T u s a t = 0 := by
      funext data
      simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, h]
    rw [hz, condExp_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Weighted source conditional square is the weighted true-row variance. -/
theorem qChiFixedFluctuation_condExp_sq (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action)
    (h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u) :
    (qSamplingLaw M T)[(fun data ↦ (qChiFixedFluctuationIncrement M v η T u s a t data)^2) |
      qPastSigma T t] =ᵐ[qSamplingLaw M T] fun _ ↦
      (M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (v) := by
  let w := M.discount * qPositiveWeight η u (t+1)
  have heq : (fun data : QSamples State Action T ↦
      (qChiFixedFluctuationIncrement M v η T u s a t data)^2) =
      w^2 • (fun data ↦ (qChiFixedCenteredDraw M v T t h.1 s a data)^2) := by
    funext data
    simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, h, qChiFixedCenteredDraw, w, mul_pow, smul_eq_mul]
  rw [heq]
  have hs := condExp_smul (μ := qSamplingLaw M T) (m := qPastSigma T t)
    (w^2) (fun data ↦ (qChiFixedCenteredDraw M v T t h.1 s a data)^2)
  filter_upwards [hs, qChiFixedCenteredDraw_condExp_sq M v T t h.1 s a] with data hd hv
  simpa [w, Pi.smul_apply, smul_eq_mul, hv] using hd

/-- Source schedule magnitude cap for any deterministic shifted-span value,
including both robust comparators and every inactive padded sample layer. -/
theorem qChiFixedFluctuation_source_abs_le (M : DiscountedMDP State Action)
    (v : State → ℝ) (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T u : ℕ)
    (hT : 2 ≤ T) (hu : u ≤ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (hspan : ∀ x y, |v x - v y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) (n : ℕ) (data : QSamples State Action T) :
    |qChiFixedFluctuationIncrement M v η T u s a n data| ≤
      M.discount * qSourceLateCap M.discount c₂ T * M.effectiveHorizon := by
  classical
  have hcap : 0 ≤ qSourceLateCap M.discount c₂ T := by
    unfold qSourceLateCap
    have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
    have hgap : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
    positivity
  by_cases hn : n < T ∧ T/2 < n+1 ∧ n+1 ≤ u
  · have hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1 := by
      intro k hk hku
      exact qSourceRate_unit_interval M.discount c₁ c₂ T η hT M.discount_lt_one hc₁ hc₂ hs k (hku.trans hu)
    have hw := qPositiveWeight_late_le η T u (n+1) hn.2.1 hn.2.2 hη
      (qSourceLateCap M.discount c₂ T) (fun k hk hku ↦
        qSourceRate_late_le M.discount c₁ c₂ T η hT M.discount_lt_one hc₂ hs k hk (hku.trans hu))
    have hc := qChi_abs_centered_le_of_pairwise (M.transition s a) v M.effectiveHorizon hspan
      (data ((s,a),⟨n,hn.1⟩))
    simp only [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, dif_pos hn,
      abs_mul, abs_of_nonneg (mul_nonneg M.discount_nonneg hw.1)]
    exact (mul_le_mul_of_nonneg_left hc (mul_nonneg M.discount_nonneg hw.1)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw.2 M.discount_nonneg) M.effectiveHorizon_nonneg)
  · simp only [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, dif_neg hn, abs_zero]
    exact mul_nonneg (mul_nonneg M.discount_nonneg hcap) M.effectiveHorizon_nonneg

end StatisticalRL.QLearning
