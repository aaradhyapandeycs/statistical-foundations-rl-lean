import Formalization.ModelFree.TDSharpPropagatedVariance

/-! LATE-WINDOW CONDITIONAL VARIANCE SUM.

This sums the exact late-window per-update conditional second-moment bound
while retaining its sample-dependent proxy. It does not prove the sharp energy
estimate, any deterministic proxy cap, or Freedman concentration.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpVarianceSumStateMeasurable : MeasurableSpace State := ⊤

/-- The actual predictable second-moment process for the zero-padded,
fixed-terminal late-window square increments, stopped at terminal `t`. The
increments use the genuine prefix filtration `tdSampleFiltration T`. -/
noncomputable def tdSquareLateWindowPredictableVariance
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (q : State) :
    TDSamples State T → ℝ :=
  predictableSecondMomentSum (tdSamplingLaw M π T) (tdSampleFiltration T)
    (tdSquareLateWindowIncrement M π η T t V₀ q) t

/-- The source's random late-window proxy before its deterministic factor
`4 H²`: it retains the actual old-iterate row variances and the tail row
`A_(k+1:t)`. -/
noncomputable def tdSquareLateWindowRandomProxy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (barη : ℝ) (q : State)
    (data : TDSamples State T) : ℝ :=
  ∑ n ∈ Finset.range t,
    if t / 2 ≤ n then
      barη * η (n + 1) * M.discount ^ 2 *
        ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
          (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data)
    else 0

/-- The padded increment is conditionally centered at its actual strict past.
On the active window this is the centered-square martingale identity; outside
it the increment is identically zero. -/
theorem tdSquareLateWindowIncrement_condExp_zero
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (q : State) (n : ℕ) :
    (tdSamplingLaw M π T)[tdSquareLateWindowIncrement M π η T t V₀ q n |
      tdSampleFiltration T n] =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  by_cases hn : t / 2 ≤ n ∧ n < t
  · simp only [tdSquareLateWindowIncrement, if_pos hn]
    exact tdSquareTerminalIncrement_condExp_past_zero M π η T t ht V₀ q n
  · have hzero : tdSquareLateWindowIncrement M π η T t V₀ q n = 0 := by
      funext data
      simp [tdSquareLateWindowIncrement, hn]
    rw [hzero, condExp_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Cumulative late-window conditional variance is bounded by the source's
random proxy. Since every padded increment has conditional mean zero, the
predictable conditional second moments here are its actual conditional
variances. No deterministic bound on the random proxy is assumed. -/
theorem tdSquareLateWindowPredictableVariance_le_randomProxy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ)
    (hbar : ∀ k, t / 2 + 1 ≤ k → k ≤ t → η k ≤ barη)
    (q : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdSquareLateWindowPredictableVariance M π η T t V₀ q data ≤
      4 * M.effectiveHorizon ^ 2 *
          tdSquareLateWindowRandomProxy M π η T t V₀ barη q data := by
  have hpoint (n : ℕ) : ∀ᵐ data ∂tdSamplingLaw M π T,
      (tdSamplingLaw M π T)[(fun data ↦
        tdSquareLateWindowIncrement M π η T t V₀ q n data ^ 2) |
          tdSampleFiltration T n] data ≤
      if t / 2 ≤ n ∧ n < t then
        4 * M.effectiveHorizon ^ 2 *
          (barη * η (n + 1) * M.discount ^ 2 *
            ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
              (M.policyTransition π r).variance
                (tdValueBefore M π η T n V₀ data))
      else 0 := by
    by_cases hn : t / 2 ≤ n ∧ n < t
    · have hstep := tdSquareLateWindowIncrement_condExp_sq_le_sourceProxy
        M π η T t ht V₀ h₀ hη n hn.1 hn.2 barη
        (hbar (n + 1) (by omega) (by omega)) q
      filter_upwards [hstep] with data hdata
      simpa [hn, mul_assoc, mul_left_comm, mul_comm] using hdata
    · have hzero : tdSquareLateWindowIncrement M π η T t V₀ q n = 0 := by
        funext d
        simp [tdSquareLateWindowIncrement, hn]
      have hzeroSq : (fun d : TDSamples State T ↦
          tdSquareLateWindowIncrement M π η T t V₀ q n d ^ 2) = 0 := by
        funext d
        simp [hzero]
      filter_upwards [] with data
      rw [hzeroSq, condExp_zero]
      simp [hn]
  have hall := ae_all_iff.mpr hpoint
  filter_upwards [hall] with data hdata
  unfold tdSquareLateWindowPredictableVariance
    predictableSecondMomentSum
    tdSquareLateWindowRandomProxy
  calc
    _ ≤ ∑ n ∈ Finset.range t,
        if t / 2 ≤ n ∧ n < t then
          4 * M.effectiveHorizon ^ 2 * barη *
            (η (n + 1) * M.discount ^ 2 *
              ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
                (M.policyTransition π r).variance
                  (tdValueBefore M π η T n V₀ data))
        else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [mul_assoc] using hdata n
    _ = 4 * M.effectiveHorizon ^ 2 *
        ∑ n ∈ Finset.range t,
          if t / 2 ≤ n then
            barη * η (n + 1) * M.discount ^ 2 *
              ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
                (M.policyTransition π r).variance
                  (tdValueBefore M π η T n V₀ data)
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnlt : n < t := Finset.mem_range.mp hn
      by_cases hnlate : t / 2 ≤ n
      · simp [hnlate, hnlt, mul_assoc, mul_left_comm, mul_comm]
      · simp [hnlate]

end StatisticalRL.TemporalDifference
