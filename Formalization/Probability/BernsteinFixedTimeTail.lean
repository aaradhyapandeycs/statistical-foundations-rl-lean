import Formalization.Probability.BernsteinExponentialProcess
import Formalization.Probability.BoundedIncrementFixedTimeTail

/-! Fixed-time variance-restricted tails from the sharp Bernstein
exponential supermartingale. -/
open MeasureTheory
open scoped BigOperators
namespace StatisticalRL
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- The actual compensated exponential has expectation at most one. -/
theorem bernsteinExponentialProcess_integral_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B < 3)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ) :
    ∫ ω, bernsteinExponentialProcess μ ℱ X B t n ω ∂μ ≤ 1 := by
  have hs := bernsteinExponentialProcess_supermartingale μ ℱ X B t hB hX hb ht hc
  have hi := hs.setIntegral_le (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, bernsteinExponentialProcess,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

/-- Markov bound on a fixed-time upper tail restricted by the actual random
predictable variance; the legal tuning parameter is explicit. -/
theorem bernstein_variance_restricted_chernoff
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B) (ht0 : 0 ≤ t)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B < 3)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ) (x v : ℝ) :
    μ.real {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤
      Real.exp (bernsteinCoefficient B t * v - t * x) := by
  let Z := bernsteinExponentialProcess μ ℱ X B t
  let a := Real.exp (t * x - bernsteinCoefficient B t * v)
  have hs := bernsteinExponentialProcess_supermartingale μ ℱ X B t hB hX hb ht hc
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω ↦ (bernsteinExponentialProcess_pos μ ℱ X B t n ω).le)
    (hs.integrable n) a
  have hi := bernsteinExponentialProcess_integral_le_one μ ℱ X B t hB hX hb ht hc n
  have hsub : {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ⊆
      {ω | a ≤ Z n ω} := by
    intro ω hω
    change a ≤ bernsteinExponentialProcess μ ℱ X B t n ω
    rw [bernsteinExponentialProcess_eq_exp_sum]
    apply Real.exp_le_exp.mpr
    have hy := mul_le_mul_of_nonneg_left hω.1 ht0
    have hv := mul_le_mul_of_nonneg_left hω.2 (bernsteinCoefficient_nonneg B t ht)
    change t * x - bernsteinCoefficient B t * v ≤ _
    change t * x ≤ t * (∑ k ∈ Finset.range n, X k ω) at hy
    change bernsteinCoefficient B t * (∑ k ∈ Finset.range n, μ[fun ω' ↦ X k ω' ^ 2 | ℱ k] ω) ≤ bernsteinCoefficient B t * v at hv
    linarith
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have ha : 0 < a := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hmono ha.le
  have hfin : a * μ.real {ω | x ≤ incrementSum X n ω ∧
      predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤ 1 := hmul.trans (hm.trans hi)
  calc
    _ ≤ 1 / a := (le_div_iff₀ ha).2 (by linarith [hfin])
    _ = Real.exp (bernsteinCoefficient B t * v - t * x) := by
      dsimp [a]
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring

/-- Exact sharp Bernstein tuning at a strictly positive variance ceiling. -/
theorem bernstein_exact_tuning (B x v : ℝ) (hB : 0 ≤ B) (hx : 0 < x) (hv : 0 < v) :
    let t := x / (v + B * x / 3)
    0 ≤ t ∧ |t| * B < 3 ∧
      bernsteinCoefficient B t * v - t * x = -x ^ 2 / (2 * (v + B * x / 3)) := by
  dsimp
  let D := v + B * x / 3
  have hD : 0 < D := by dsimp [D]; positivity
  have ht : 0 ≤ x / D := div_nonneg hx.le hD.le
  have hlegal : |x / D| * B < 3 := by
    rw [abs_of_nonneg ht, div_mul_eq_mul_div]
    apply (div_lt_iff₀ hD).2
    dsimp [D]
    nlinarith
  refine ⟨ht, hlegal, ?_⟩
  have hden : 1 - |x / D| * B / 3 = v / D := by
    rw [abs_of_nonneg ht]
    dsimp [D]
    field_simp
    ring
  unfold bernsteinCoefficient
  rw [hden]
  change (x / D) ^ 2 / (2 * (v / D)) * v - x / D * x = -x ^ 2 / (2 * D)
  field_simp
  ring

/-- Sharp Bernstein fixed-time variance-restricted upper tail. -/
theorem bernstein_variance_restricted_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ)
    (x v : ℝ) (hx : 0 < x) (hv : 0 < v) :
    μ.real {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤
      Real.exp (-x ^ 2 / (2 * (v + B * x / 3))) := by
  obtain ⟨ht, hlegal, he⟩ := bernstein_exact_tuning B x v hB hx hv
  have hp := bernstein_variance_restricted_chernoff μ ℱ X B _ hB ht hX hb hlegal hc n x v
  rw [he] at hp
  exact hp

/-- Radius chosen for the exact source Freedman peeling constants. -/
theorem bernstein_source_radius_arithmetic (B v L : ℝ)
    (hB : 0 ≤ B) (hv : 0 < v) (hL : 0 < L) :
    let x := 2 * Real.sqrt (v * L) + (4 / 3) * B * L
    0 < x ∧ L ≤ x ^ 2 / (2 * (v + B * x / 3)) := by
  dsimp
  have hr := Real.sqrt_nonneg (v * L)
  have hrpos : 0 < Real.sqrt (v * L) := Real.sqrt_pos.mpr (mul_pos hv hL)
  have hr2 := Real.sq_sqrt (mul_nonneg hv.le hL.le)
  have hx : 0 < 2 * Real.sqrt (v * L) + (4 / 3) * B * L := by positivity
  refine ⟨hx, (le_div_iff₀ (by positivity)).2 ?_⟩
  nlinarith [mul_nonneg (mul_nonneg hB hL.le) hr,
    sq_nonneg (B * L)]

/-- Fixed-time one-sided tail with the linear coefficient four-thirds needed
by the source, before the two-sign and dyadic-variance union. -/
theorem bernstein_variance_restricted_source_radius
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ)
    (v L : ℝ) (hv : 0 < v) (hL : 0 < L) :
    μ.real {ω | 2 * Real.sqrt (v * L) + (4 / 3) * B * L ≤ incrementSum X n ω ∧
      predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤ Real.exp (-L) := by
  obtain ⟨hx, he⟩ := bernstein_source_radius_arithmetic B v L hB hv hL
  exact (bernstein_variance_restricted_tail μ ℱ X B hB hX hb hc n _ v hx hv).trans
    (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg he))

end StatisticalRL
