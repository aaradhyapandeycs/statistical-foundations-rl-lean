import Formalization.ModelFree.QLearningOptimalFluctuation
import Formalization.ModelFree.QLearningConditionalPullout

/-! Actual conditional moments of the source's fixed-optimal-value fluctuation. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptMomentStateMeasurable : MeasurableSpace State := ⊤
local instance qOptMomentActionMeasurable : MeasurableSpace Action := ⊤

/-- Nonnegative source weight under the actual rate-prefix assumptions. -/
theorem qPositiveWeight_nonneg (η : ℕ → ℝ) (u i : ℕ) (hi : 1 ≤ i) (hiu : i ≤ u)
    (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1) :
    0 ≤ qPositiveWeight η u i := by
  unfold qPositiveWeight
  apply mul_nonneg (hη i hi hiu).1
  apply Finset.prod_nonneg
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  exact sub_nonneg.mpr (hη j (by omega) hj'.2).2

/-- Actual optimal trajectory value has the source return interval. -/
theorem qTrueOptimalValue_bounds (M : DiscountedMDP State Action) (x : State) :
    0 ≤ qTrueOptimalValue M x ∧ qTrueOptimalValue M x ≤ M.effectiveHorizon := by
  simpa [qTrueOptimalValue, DiscountedMDP.effectiveHorizon] using
    M.trajectoryExpectedValue_bounds M.optimalGreedyPolicy x

/-- The one-row fixed-value centered draw, before the deterministic source weight. -/
noncomputable def qOptimalCenteredDraw (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) (data : QSamples State Action T) : ℝ :=
  qTrueOptimalValue M (data ((s,a), ⟨t,ht⟩)) -
    (M.transition s a).expectation (qTrueOptimalValue M)

/-- Conditional mean of the actual fixed-V* centered draw is zero. -/
theorem qOptimalCenteredDraw_condExp_zero (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) :
    (qSamplingLaw M T)[qOptimalCenteredDraw M T t ht s a | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  classical
  let c : State → QSamples State Action T → ℝ := fun x _ ↦ qTrueOptimalValue M x
  have heq : (fun data : QSamples State Action T ↦ qTrueOptimalValue M
      (data ((s,a), ⟨t,ht⟩))) = ∑ x, c x * qFreshIndicator T t ht s a x := by
    funext data
    simp [c, qFreshIndicator, Finset.sum_apply]
  have hs := qFresh_predictable_sum_condExp M T t ht s a c (fun _ ↦ stronglyMeasurable_const)
  have hmean : (qSamplingLaw M T)[(fun data ↦ qTrueOptimalValue M
      (data ((s,a), ⟨t,ht⟩))) | qPastSigma T t] =ᵐ[qSamplingLaw M T]
      fun _ ↦ (M.transition s a).expectation (qTrueOptimalValue M) := by
    rw [heq]
    filter_upwards [hs] with data hd
    simpa [c, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd
  have hsub := condExp_sub (qSampling_integrable M T (fun data ↦ qTrueOptimalValue M
      (data ((s,a), ⟨t,ht⟩)))) (qSampling_integrable M T (fun _ ↦
      (M.transition s a).expectation (qTrueOptimalValue M))) (qPastSigma T t)
  have hc := condExp_const (μ := qSamplingLaw M T) (qPastSigma_le T t)
      ((M.transition s a).expectation (qTrueOptimalValue M))
  change (qSamplingLaw M T)[(fun data ↦ qTrueOptimalValue M (data ((s,a), ⟨t,ht⟩))) -
    (fun _ ↦ (M.transition s a).expectation (qTrueOptimalValue M)) | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0
  filter_upwards [hsub, hmean] with data hd hm
  rw [hc] at hd
  simp only [Pi.sub_apply, hm, sub_self] at hd
  exact hd

/-- The fixed-V* squared draw has exactly its true-row conditional variance. -/
theorem qOptimalCenteredDraw_condExp_sq (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) :
    (qSamplingLaw M T)[(fun data ↦ (qOptimalCenteredDraw M T t ht s a data)^2) | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ qRowVariance M s a (qTrueOptimalValue M) := by
  classical
  let c : State → QSamples State Action T → ℝ := fun x _ ↦
    (qTrueOptimalValue M x - (M.transition s a).expectation (qTrueOptimalValue M))^2
  have heq : (fun data : QSamples State Action T ↦ (qOptimalCenteredDraw M T t ht s a data)^2) =
      ∑ x, c x * qFreshIndicator T t ht s a x := by
    funext data
    simp [c, qOptimalCenteredDraw, qFreshIndicator, Finset.sum_apply]
  rw [heq]
  have h := qFresh_predictable_sum_condExp M T t ht s a c (fun _ ↦ stronglyMeasurable_const)
  filter_upwards [h] with data hd
  simpa [c, qRowVariance, qRowMean, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd

/-- Weighted source fluctuation is conditionally centered, including inactive layers. -/
theorem qOptimalFluctuation_condExp_zero (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    (qSamplingLaw M T)[qOptimalFluctuationIncrement M η T u s a t | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  classical
  by_cases h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u
  · let w := M.discount * qPositiveWeight η u (t+1)
    have heq : qOptimalFluctuationIncrement M η T u s a t =
        w • qOptimalCenteredDraw M T t h.1 s a := by
      funext data
      simp [qOptimalFluctuationIncrement, h, qOptimalCenteredDraw, w, smul_eq_mul]
    rw [heq]
    have hs := condExp_smul (μ := qSamplingLaw M T) (m := qPastSigma T t)
      w (qOptimalCenteredDraw M T t h.1 s a)
    have hz := qOptimalCenteredDraw_condExp_zero M T t h.1 s a
    filter_upwards [hs, hz] with data hd hz'
    simpa [Pi.smul_apply, smul_eq_mul, hz'] using hd
  · have hz : qOptimalFluctuationIncrement M η T u s a t = 0 := by
      funext data
      simp [qOptimalFluctuationIncrement, h]
    rw [hz, condExp_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Weighted source conditional square is the weighted true-row variance. -/
theorem qOptimalFluctuation_condExp_sq (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action)
    (h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u) :
    (qSamplingLaw M T)[(fun data ↦ (qOptimalFluctuationIncrement M η T u s a t data)^2) |
      qPastSigma T t] =ᵐ[qSamplingLaw M T] fun _ ↦
      (M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (qTrueOptimalValue M) := by
  let w := M.discount * qPositiveWeight η u (t+1)
  have heq : (fun data : QSamples State Action T ↦
      (qOptimalFluctuationIncrement M η T u s a t data)^2) =
      w^2 • (fun data ↦ (qOptimalCenteredDraw M T t h.1 s a data)^2) := by
    funext data
    simp [qOptimalFluctuationIncrement, h, qOptimalCenteredDraw, w, mul_pow, smul_eq_mul]
  rw [heq]
  have hs := condExp_smul (μ := qSamplingLaw M T) (m := qPastSigma T t)
    (w^2) (fun data ↦ (qOptimalCenteredDraw M T t h.1 s a data)^2)
  filter_upwards [hs, qOptimalCenteredDraw_condExp_sq M T t h.1 s a] with data hd hv
  simpa [w, Pi.smul_apply, smul_eq_mul, hv] using hd

/- Nonnegativity is needed only for removing |w| in magnitude bounds,
not for moment identities. Transfer prefix moments to the smaller natural history
with a proved tower/adaptation bridge; no independence of random η is assumed.
-/
end StatisticalRL.QLearning
