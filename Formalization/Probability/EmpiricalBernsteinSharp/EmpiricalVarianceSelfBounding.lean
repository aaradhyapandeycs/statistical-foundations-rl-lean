import Formalization.Probability.EmpiricalBernsteinSelfNormalized

/-! Private source-only deterministic preparation for the sharp empirical
Bernstein route. This file asserts no concentration or source theorem. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance sharpSelfBoundStateMeasurable : MeasurableSpace State := ⊤

/-- N times the unbiased empirical variance after normalization to [0,1]. -/
noncomputable def normalizedUnbiasedVariance (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (ω : Fin N → State) : ℝ :=
  let hN : 0 < N := by omega
  ((N : ℝ)^2 / (((N : ℝ) - 1) * B^2)) * empiricalVariance N hN V ω

/-- The coordinate-free lower envelope induced by the leave-one-out residual. -/
noncomputable def normalizedUnbiasedVarianceRemoved (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (ω : Fin N → State) (i : Fin N) : ℝ :=
  ((N : ℝ)^2 / (((N : ℝ) - 1) * B^2)) * leaveOneOutResidual N hN2 V ω i

/-- The normalized statistic is nonnegative on every sample. -/
theorem normalizedUnbiasedVariance_nonneg (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (hB : 0 < B) (ω : Fin N → State) :
    0 ≤ normalizedUnbiasedVariance N hN2 V B ω := by
  let hN : 0 < N := by omega
  unfold normalizedUnbiasedVariance
  apply mul_nonneg
  · have hn : 0 < (N : ℝ) - 1 := by
      have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      linarith
    positivity
  · exact empiricalVariance_nonneg N hN V ω

/-- The normalization has expectation N times the true variance divided by B². -/
theorem normalizedUnbiasedVariance_integral (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (V : State → ℝ) (B : ℝ) (hB : 0 < B) :
    ∫ ω, normalizedUnbiasedVariance N hN2 V B ω ∂(d.sampleMeasure N) =
      (N : ℝ) * d.variance V / B^2 := by
  let hN : 0 < N := by omega
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hb : B ≠ 0 := ne_of_gt hB
  simp only [normalizedUnbiasedVariance, integral_const_mul,
    d.empiricalVariance_integral N hN V]
  field_simp [hn, hn1, hb]

/-- The lower envelope is unaffected by changing the removed coordinate. -/
theorem normalizedUnbiasedVarianceRemoved_congr (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (ω ω' : Fin N → State) (i : Fin N)
    (h : ∀ j, j ≠ i → ω j = ω' j) :
    normalizedUnbiasedVarianceRemoved N hN2 V B ω i =
      normalizedUnbiasedVarianceRemoved N hN2 V B ω' i := by
  unfold normalizedUnbiasedVarianceRemoved
  rw [leaveOneOutResidual_congr N hN2 V ω ω' i h]

/-- Each normalized deletion decrement lies in [0,1], and their squared
sum is bounded by N/(N−1) times the normalized unbiased sample variance. -/
theorem normalizedUnbiasedVariance_decrements (N : ℕ) (hN2 : 2 ≤ N)
    (V : State → ℝ) (B : ℝ) (hB : 0 < B)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) (ω : Fin N → State) :
    (∀ i : Fin N, 0 ≤ normalizedUnbiasedVariance N hN2 V B ω -
        normalizedUnbiasedVarianceRemoved N hN2 V B ω i ∧
      normalizedUnbiasedVariance N hN2 V B ω -
        normalizedUnbiasedVarianceRemoved N hN2 V B ω i ≤ 1) ∧
    (∑ i : Fin N, (normalizedUnbiasedVariance N hN2 V B ω -
      normalizedUnbiasedVarianceRemoved N hN2 V B ω i)^2) ≤
      (N : ℝ) / ((N : ℝ) - 1) * normalizedUnbiasedVariance N hN2 V B ω := by
  let hN : 0 < N := by omega
  let c : ℝ := (N : ℝ)^2 / (((N : ℝ) - 1) * B^2)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have heq (i : Fin N) :
      normalizedUnbiasedVariance N hN2 V B ω -
          normalizedUnbiasedVarianceRemoved N hN2 V B ω i =
        c * (empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i) := by
    simp only [normalizedUnbiasedVariance, normalizedUnbiasedVarianceRemoved, c, mul_sub]
  constructor
  · intro i
    rw [heq]
    have h0 := empiricalVariance_leaveOneOut_decrement_nonneg N hN2 V ω i
    have h1 := empiricalVariance_leaveOneOut_decrement_le_sharp N hN2 V B hV ω i
    constructor
    · exact mul_nonneg hc h0
    · calc
        c * (empiricalVariance N hN V ω - leaveOneOutResidual N hN2 V ω i) ≤
            c * (((N : ℝ) - 1) / (N : ℝ)^2 * B^2) :=
          mul_le_mul_of_nonneg_left h1 hc
        _ = 1 := by dsimp [c]; field_simp [ne_of_gt hn, ne_of_gt hn1, ne_of_gt hB] <;> ring
  · simp_rw [heq, mul_pow]
    rw [← Finset.mul_sum]
    have hb := sum_sq_empiricalVariance_leaveOneOut_decrement_le_sharp N hN2 V B hV ω
    calc
      c^2 * ∑ i : Fin N, (empiricalVariance N hN V ω -
          leaveOneOutResidual N hN2 V ω i)^2 ≤
          c^2 * (B^2 / (N : ℝ) * empiricalVariance N hN V ω) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg c)
      _ = (N : ℝ) / ((N : ℝ) - 1) * normalizedUnbiasedVariance N hN2 V B ω := by
        simp only [normalizedUnbiasedVariance, c]
        field_simp [ne_of_gt hn, ne_of_gt hn1, ne_of_gt hB]
end StatisticalRL.FiniteDistribution
