import Formalization.Probability.BoundedIncrementExponentialProcess

/-! Fixed-time variance-restricted tails from the preliminary quadratic
exponential supermartingale; no sharp Freedman constants are claimed. -/
open MeasureTheory
open scoped BigOperators
namespace StatisticalRL
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

def incrementSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, X k ω

noncomputable def predictableSecondMomentSum (μ : Measure Ω)
    (ℱ : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, μ[fun ω' ↦ X k ω' ^ 2 | ℱ k] ω

/-- The actual compensated exponential has expectation at most one. -/
theorem boundedIncrementExponentialProcess_integral_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B ≤ 1)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ) :
    ∫ ω, boundedIncrementExponentialProcess μ ℱ X t n ω ∂μ ≤ 1 := by
  have hs := boundedIncrementExponentialProcess_supermartingale μ ℱ X B t hB hX hb ht hc
  have hi := hs.setIntegral_le (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, boundedIncrementExponentialProcess,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

/-- Markov bound on a fixed-time upper tail restricted by the actual random
predictable variance; the legal tuning parameter is explicit. -/
theorem boundedIncrement_variance_restricted_chernoff
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B t : ℝ) (hB : 0 ≤ B) (ht0 : 0 ≤ t)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B) (ht : |t| * B ≤ 1)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ) (x v : ℝ) :
    μ.real {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤
      Real.exp (t ^ 2 * v - t * x) := by
  let Z := boundedIncrementExponentialProcess μ ℱ X t
  let a := Real.exp (t * x - t ^ 2 * v)
  have hs := boundedIncrementExponentialProcess_supermartingale μ ℱ X B t hB hX hb ht hc
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω ↦ (boundedIncrementExponentialProcess_pos μ ℱ X t n ω).le)
    (hs.integrable n) a
  have hi := boundedIncrementExponentialProcess_integral_le_one μ ℱ X B t hB hX hb ht hc n
  have hsub : {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ⊆
      {ω | a ≤ Z n ω} := by
    intro ω hω
    change a ≤ boundedIncrementExponentialProcess μ ℱ X t n ω
    rw [boundedIncrementExponentialProcess_eq_exp_sum]
    apply Real.exp_le_exp.mpr
    have hy := mul_le_mul_of_nonneg_left hω.1 ht0
    have hv := mul_le_mul_of_nonneg_left hω.2 (sq_nonneg t)
    change t * x - t ^ 2 * v ≤ _
    change t * x ≤ t * (∑ k ∈ Finset.range n, X k ω) at hy
    change t ^ 2 * (∑ k ∈ Finset.range n, μ[fun ω' ↦ X k ω' ^ 2 | ℱ k] ω) ≤ t ^ 2 * v at hv
    linarith
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have ha : 0 < a := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hmono ha.le
  have hfin : a * μ.real {ω | x ≤ incrementSum X n ω ∧
      predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤ 1 := hmul.trans (hm.trans hi)
  calc
    _ ≤ 1 / a := (le_div_iff₀ ha).2 (by linarith [hfin])
    _ = Real.exp (t ^ 2 * v - t * x) := by
      dsimp [a]
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring

/-- A legal rational tuning yields a Bernstein-shaped exponent for every
positive B,x and nonnegative variance scale v, including v=0. -/
theorem boundedIncrement_quadratic_tuning (B x v : ℝ)
    (hB : 0 < B) (hx : 0 < x) (hv : 0 ≤ v) :
    let t := x / (2 * v + B * x)
    0 ≤ t ∧ |t| * B ≤ 1 ∧
      t ^ 2 * v - t * x ≤ -x ^ 2 / (4 * v + 2 * B * x) := by
  dsimp
  let D := 2 * v + B * x
  have hD : 0 < D := by dsimp [D]; positivity
  have ht : 0 ≤ x / D := div_nonneg hx.le hD.le
  have heq : (x / D) * D = x := div_mul_cancel₀ _ hD.ne'
  refine ⟨ht, ?_, ?_⟩
  · rw [abs_of_nonneg ht]
    dsimp [D] at *
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hD).2
    nlinarith
  · have htv : (x / D) * v ≤ x / 2 := by
      dsimp [D] at heq
      nlinarith [mul_nonneg ht (mul_nonneg hB.le hx.le)]
    have hp := mul_le_mul_of_nonneg_left htv ht
    have hid : -x ^ 2 / (4 * v + 2 * B * x) = -(x / D * x) / 2 := by
      have hd2 : 4 * v + 2 * B * x = 2 * D := by dsimp [D]; ring
      rw [hd2]
      field_simp
    rw [hid]
    nlinarith

/-- Actual fixed-time variance-restricted upper tail with the constants
justified by the preliminary t² compensator. -/
theorem boundedIncrement_variance_restricted_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 < B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ)
    (x v : ℝ) (hx : 0 < x) (hv : 0 ≤ v) :
    μ.real {ω | x ≤ incrementSum X n ω ∧ predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤
      Real.exp (-x ^ 2 / (4 * v + 2 * B * x)) := by
  obtain ⟨ht, hlegal, he⟩ := boundedIncrement_quadratic_tuning B x v hB hx hv
  exact (boundedIncrement_variance_restricted_chernoff μ ℱ X B _ hB.le ht hX hb hlegal hc n x v).trans
    (Real.exp_le_exp.mpr he)

/-- A transparent radius conversion for the proved exponent. Its linear
coefficient is two, rather than the source Freedman coefficient four-thirds. -/
theorem boundedIncrement_radius_arithmetic (B v L : ℝ)
    (hB : 0 < B) (hv : 0 ≤ v) (hL : 0 < L) :
    let x := 2 * Real.sqrt (v * L) + 2 * B * L
    0 < x ∧ L ≤ x ^ 2 / (4 * v + 2 * B * x) := by
  dsimp
  have hr := Real.sqrt_nonneg (v * L)
  have hr2 := Real.sq_sqrt (mul_nonneg hv hL.le)
  have hx : 0 < 2 * Real.sqrt (v * L) + 2 * B * L := by positivity
  refine ⟨hx, (le_div_iff₀ (by positivity)).2 ?_⟩
  nlinarith [mul_nonneg (mul_nonneg hB.le hL.le) hr]

/-- A fixed-time variance-restricted confidence radius justified entirely by
the proved preliminary supermartingale and a legal tuning parameter. -/
theorem boundedIncrement_variance_restricted_radius
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (X : ℕ → Ω → ℝ) (B : ℝ) (hB : 0 < B)
    (hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ B)
    (hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0) (n : ℕ)
    (v L : ℝ) (hv : 0 ≤ v) (hL : 0 < L) :
    μ.real {ω | 2 * Real.sqrt (v * L) + 2 * B * L ≤ incrementSum X n ω ∧
      predictableSecondMomentSum μ ℱ X n ω ≤ v} ≤ Real.exp (-L) := by
  obtain ⟨hx, he⟩ := boundedIncrement_radius_arithmetic B v L hB hv hL
  exact (boundedIncrement_variance_restricted_tail μ ℱ X B hB hX hb hc n _ v hx hv).trans
    (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg he))

end StatisticalRL
