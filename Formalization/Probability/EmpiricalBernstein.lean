import Formalization.Probability.EmpiricalHoeffding
import Formalization.Probability.Variance
import Mathlib.Probability.Moments.Variance

/-!
# Variance and moment-generating functions of actual iid row samples

These are prerequisites for a fixed-vector Bernstein bound. No Bernstein tail
estimate is assumed or claimed here. Source: arXiv:2610.41903v1, Lemma 2.5.
-/

open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance empiricalBernsteinStateMeasurable : MeasurableSpace State := ⊤

/-- Every sampled value is measurable on the actual product sample space. -/
theorem sampleValue_measurable (V : State → ℝ) (N : ℕ) (i : Fin N) :
    Measurable (fun ω : Fin N → State ↦ V (ω i)) :=
  (measurable_of_countable V).comp (measurable_pi_apply i)

/-- Every sampled value has a finite second moment. -/
theorem sampleValue_memLp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (i : Fin N) :
    MemLp (fun ω : Fin N → State ↦ V (ω i)) 2 (d.sampleMeasure N) := by
  apply MemLp.of_bound (sampleValue_measurable V N i).aestronglyMeasurable ‖V‖
  filter_upwards with ω
  exact norm_le_pi_norm V (ω i)

/-- The measure-theoretic variance of each draw is the source's finite-row variance. -/
theorem sampleValue_variance (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (i : Fin N) :
    ProbabilityTheory.variance (fun ω : Fin N → State ↦ V (ω i)) (d.sampleMeasure N) =
      d.variance V := by
  rw [ProbabilityTheory.variance_eq_integral (sampleValue_measurable V N i).aemeasurable,
    d.sampleMeasure_coordinate_integral N i V, d.variance_eq_expectation_centered_sq]
  exact d.sampleMeasure_coordinate_integral N i (fun s ↦ (V s - d.expectation V) ^ 2)

/-- The values of the independent state samples remain independent. -/
theorem sampleValue_independent (d : FiniteDistribution State) (V : State → ℝ) (N : ℕ) :
    iIndepFun (fun i (ω : Fin N → State) ↦ V (ω i)) (d.sampleMeasure N) := by
  exact (d.sampleMeasure_independent N).comp (fun _ ↦ V) (fun _ ↦ measurable_of_countable V)

/-- The variance of the actual sum of N observations is N times the row variance. -/
theorem sampleSum_variance (d : FiniteDistribution State) (V : State → ℝ) (N : ℕ) :
    ProbabilityTheory.variance (fun ω : Fin N → State ↦ ∑ i : Fin N, V (ω i))
      (d.sampleMeasure N) = (N : ℝ) * d.variance V := by
  let X : Fin N → (Fin N → State) → ℝ := fun i ω ↦ V (ω i)
  have hind : iIndepFun X (d.sampleMeasure N) := d.sampleValue_independent V N
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin N)), MemLp (X i) 2 (d.sampleMeasure N) :=
    fun i _ ↦ d.sampleValue_memLp V N i
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin N)))
      (fun i j ↦ IndepFun (X i) (X j) (d.sampleMeasure N)) := by
    intro i hi j hj hij
    exact hind.indepFun hij
  have hvar := IndepFun.variance_sum (X := X) (s := Finset.univ) hmem hpair
  have heq : (∑ i : Fin N, X i) = (fun ω : Fin N → State ↦ ∑ i : Fin N, V (ω i)) := by
    funext ω
    simp [X]
  rw [heq] at hvar
  rw [hvar]
  simp [X, sampleValue_variance]

/-- Every empirical-row evaluation has a finite second moment. -/
theorem empiricalValue_memLp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) :
    MemLp (fun ω ↦ (empiricalRow N hN ω).expectation V) 2 (d.sampleMeasure N) := by
  apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable ‖V‖
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (empiricalRow N hN ω).abs_expectation_le (fun s ↦ by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)

/-- The empirical evaluation has variance exactly the row variance divided by N. -/
theorem empiricalValue_variance (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) :
    ProbabilityTheory.variance (fun ω ↦ (empiricalRow N hN ω).expectation V)
      (d.sampleMeasure N) = d.variance V / N := by
  simp_rw [empiricalRow_expectation]
  rw [ProbabilityTheory.variance_const_mul, d.sampleSum_variance]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp

/-- A variance-sensitive polynomial tail follows from Chebyshev for the
actual empirical row. This is not the desired exponential Bernstein bound. -/
theorem empiricalRow_chebyshev (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    d.sampleMeasure N {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      ENNReal.ofReal (d.variance V / ((N : ℝ) * ε ^ 2)) := by
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq (d.empiricalValue_memLp V N hN) hε
  rw [d.empiricalRow_unbiased N hN V, d.empiricalValue_variance V N hN] at h
  simpa only [div_div] using h

/-- Independence factors the MGF of the centered sample sum exactly. -/
theorem centeredSample_mgf_factor (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (u : ℝ) :
    ProbabilityTheory.mgf (fun ω ↦ ∑ i : Fin N, d.centeredSample V N i ω)
      (d.sampleMeasure N) u =
      ∏ i : Fin N, ProbabilityTheory.mgf (d.centeredSample V N i) (d.sampleMeasure N) u := by
  have h := (d.centeredSample_independent V N).mgf_sum
    (fun i ↦ (sampleValue_measurable V N i).sub measurable_const) Finset.univ (t := u)
  have heq : (∑ i : Fin N, d.centeredSample V N i) =
      (fun ω ↦ ∑ i : Fin N, d.centeredSample V N i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [heq] at h
  exact h

/-- Every centered coordinate has the MGF of the actual transition row. -/
theorem centeredSample_mgf_eq_row (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (i : Fin N) (u : ℝ) :
    ProbabilityTheory.mgf (d.centeredSample V N i) (d.sampleMeasure N) u =
      ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u := by
  unfold ProbabilityTheory.mgf centeredSample
  calc
    (∫ ω, Real.exp (u * (V (ω i) - d.expectation V)) ∂d.sampleMeasure N) =
        d.expectation (fun s ↦ Real.exp (u * (V s - d.expectation V))) :=
      d.sampleMeasure_coordinate_integral N i (fun s ↦ Real.exp (u * (V s - d.expectation V)))
    _ = ∫ s, Real.exp (u * (V s - d.expectation V)) ∂d.rowMeasure :=
      (d.rowMeasure_integral _).symm

/-- The centered sample sum has the Nth power of the actual row MGF. -/
theorem centeredSample_mgf_pow (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (u : ℝ) :
    ProbabilityTheory.mgf (fun ω ↦ ∑ i : Fin N, d.centeredSample V N i ω)
      (d.sampleMeasure N) u =
      (ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u) ^ N := by
  rw [d.centeredSample_mgf_factor V N u]
  simp [d.centeredSample_mgf_eq_row]

/-- Chernoff bound for the actual empirical mean, retaining the exact row MGF.
No variance-sensitive upper bound on that MGF is assumed. -/
theorem empiricalRow_chernoff_mgf (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ε u : ℝ) (hu : 0 ≤ u) :
    (d.sampleMeasure N).real {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} ≤
      Real.exp (-u * ((N : ℝ) * ε)) *
        (ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u) ^ N := by
  have hint : Integrable (fun ω : Fin N → State ↦
      Real.exp (u * ∑ i : Fin N, d.centeredSample V N i ω)) (d.sampleMeasure N) :=
    Integrable.of_finite
  have h := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := fun ω : Fin N → State ↦ ∑ i : Fin N, d.centeredSample V N i ω)
    ((N : ℝ) * ε) hu hint
  rw [d.centeredSample_mgf_pow V N u] at h
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hevent : {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, d.centeredSample V N i ω} =
      {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} := by
    ext ω
    change (N : ℝ) * ε ≤ ∑ i : Fin N, d.centeredSample V N i ω ↔ _
    rw [d.centeredSum_eq_empirical V N hN ω]
    exact mul_le_mul_iff_right₀ hn
  rw [hevent] at h
  exact h

/-- If the true row variance is zero, any positive empirical deviation has
probability zero. -/
theorem empiricalRow_zeroVariance_tail (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hvar : d.variance V = 0) :
    d.sampleMeasure N {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} = 0 := by
  apply le_antisymm _ bot_le
  simpa [hvar] using d.empiricalRow_chebyshev V N hN ε hε

/-- A direct variance-sensitive bound for the actual centered row MGF in the
restricted range `u * B ≤ 1`. This quadratic bound is weaker than the sharp
Bernstein MGF inequality and is not the source Bernstein theorem. -/
theorem centeredRow_mgf_le_exp_variance (d : FiniteDistribution State) (V : State → ℝ)
    (B u : ℝ) (hu : 0 ≤ u) (hsmall : u * B ≤ 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u ≤
      Real.exp (u ^ 2 * d.variance V) := by
  have hμ0 : 0 ≤ d.expectation V := d.expectation_nonneg (fun s ↦ (hV s).1)
  have hμB : d.expectation V ≤ B := d.expectation_le_const (fun s ↦ (hV s).2)
  have hc (s : State) : |V s - d.expectation V| ≤ B := by
    apply abs_le.mpr
    constructor <;> linarith [(hV s).1, (hV s).2]
  have hpoint (s : State) :
      Real.exp (u * (V s - d.expectation V)) ≤
        1 + u * (V s - d.expectation V) + u ^ 2 * (V s - d.expectation V) ^ 2 := by
    have hz : ‖u * (V s - d.expectation V)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu]
      exact (mul_le_mul_of_nonneg_left (hc s) hu).trans hsmall
    have hexp := Real.norm_exp_sub_one_sub_id_le hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at hexp
    have hle := le_abs_self (Real.exp (u * (V s - d.expectation V)) - 1 -
      u * (V s - d.expectation V))
    nlinarith [hle, hexp]
  have hmean : d.expectation (fun s ↦ V s - d.expectation V) = 0 := by
    rw [d.expectation_sub, d.expectation_const, sub_self]
  calc
    ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u =
        d.expectation (fun s ↦ Real.exp (u * (V s - d.expectation V))) := by
      exact d.rowMeasure_integral _
    _ ≤ d.expectation (fun s ↦ 1 + u * (V s - d.expectation V) +
        u ^ 2 * (V s - d.expectation V) ^ 2) := d.expectation_mono hpoint
    _ = 1 + u ^ 2 * d.variance V := by
      rw [d.expectation_add, d.expectation_add, d.expectation_const,
        d.expectation_mul, d.expectation_mul, hmean,
        ← d.variance_eq_expectation_centered_sq]
      ring
    _ ≤ Real.exp (u ^ 2 * d.variance V) := by
      linarith [Real.add_one_le_exp (u ^ 2 * d.variance V)]

/-- A variance-sensitive exponential upper tail on the actual empirical row,
valid for every tuning parameter in the proved restricted range. -/
theorem empiricalRow_upper_variance_tail (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε u : ℝ) (hu : 0 ≤ u) (hsmall : u * B ≤ 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} ≤
      Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) * (u ^ 2 * d.variance V)) := by
  have hmgf := d.centeredRow_mgf_le_exp_variance V B u hu hsmall hV
  have hnonneg : 0 ≤ ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u :=
    ProbabilityTheory.mgf_nonneg
  calc
    _ ≤ Real.exp (-u * ((N : ℝ) * ε)) *
        (ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u) ^ N :=
      d.empiricalRow_chernoff_mgf V N hN ε u hu
    _ ≤ Real.exp (-u * ((N : ℝ) * ε)) *
        (Real.exp (u ^ 2 * d.variance V)) ^ N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hmgf N) (Real.exp_nonneg _)
    _ = Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) * (u ^ 2 * d.variance V)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]

/-- Reflecting a vector about a constant preserves its true row variance. -/
theorem variance_const_sub (d : FiniteDistribution State) (V : State → ℝ) (B : ℝ) :
    d.variance (fun s ↦ B - V s) = d.variance V := by
  rw [d.variance_eq_expectation_centered_sq, d.variance_eq_expectation_centered_sq]
  have hmean : d.expectation (fun s ↦ B - V s) = B - d.expectation V := by
    rw [d.expectation_sub, d.expectation_const]
  rw [hmean]
  congr 1
  funext s
  ring

/-- Restricted-range variance-sensitive lower tail on the actual sample law. -/
theorem empiricalRow_lower_variance_tail (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε u : ℝ) (hu : 0 ≤ u) (hsmall : u * B ≤ 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ -((empiricalRow N hN ω).expectation V - d.expectation V)} ≤
      Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) * (u ^ 2 * d.variance V)) := by
  let W : State → ℝ := fun s ↦ B - V s
  have hw (s : State) : W s ∈ Set.Icc 0 B := by
    dsimp [W]
    constructor <;> linarith [(hV s).1, (hV s).2]
  have h := d.empiricalRow_upper_variance_tail W N hN B ε u hu hsmall hw
  have hvar : d.variance W = d.variance V := d.variance_const_sub V B
  rw [hvar] at h
  have hevent : {ω | ε ≤ (empiricalRow N hN ω).expectation W - d.expectation W} =
      {ω | ε ≤ -((empiricalRow N hN ω).expectation V - d.expectation V)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have h1 : (empiricalRow N hN ω).expectation W = B - (empiricalRow N hN ω).expectation V := by
      dsimp [W]
      rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]
    have h2 : d.expectation W = B - d.expectation V := by
      dsimp [W]
      rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]
    rw [h1, h2]
    ring_nf
  rwa [hevent] at h

/-- A two-sided variance-sensitive exponential bound on the actual empirical
row, for arbitrary admissible `u`; the quadratic MGF constant is not sharp. -/
theorem empiricalRow_twoSided_variance_tail (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε u : ℝ) (hu : 0 ≤ u) (hsmall : u * B ≤ 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) * (u ^ 2 * d.variance V)) := by
  let D : (Fin N → State) → ℝ := fun ω ↦ (empiricalRow N hN ω).expectation V - d.expectation V
  have hp := d.empiricalRow_upper_variance_tail V N hN B ε u hu hsmall hV
  have hn := d.empiricalRow_lower_variance_tail V N hN B ε u hu hsmall hV
  calc
    (d.sampleMeasure N).real {ω | ε ≤ |D ω|} ≤
        (d.sampleMeasure N).real ({ω | ε ≤ D ω} ∪ {ω | ε ≤ -D ω}) := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change ε ≤ |D ω| at hω
      change ε ≤ D ω ∨ ε ≤ -D ω
      exact le_abs.mp hω
    _ ≤ (d.sampleMeasure N).real {ω | ε ≤ D ω} +
        (d.sampleMeasure N).real {ω | ε ≤ -D ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) * (u ^ 2 * d.variance V)) := by
      simpa only [two_mul] using add_le_add hp hn

/-- An explicit variance-sensitive exponential tail, obtained by a valid
restricted tuning parameter. Its constants are weaker than source Bernstein. -/
theorem empiricalRow_variance_tail_explicit (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 * (d.variance V + B * ε) /
        (2 * d.variance V + B * ε) ^ 2) := by
  let D : ℝ := 2 * d.variance V + B * ε
  have hD : 0 < D := by
    dsimp [D]
    have hv := d.variance_nonneg V
    positivity
  let u : ℝ := ε / D
  have hu : 0 ≤ u := div_nonneg hε.le hD.le
  have hsmall : u * B ≤ 1 := by
    dsimp [u]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    dsimp [D]
    nlinarith [d.variance_nonneg V]
  have h := d.empiricalRow_twoSided_variance_tail V N hN B ε u hu hsmall hV
  have heq : -u * ((N : ℝ) * ε) + (N : ℝ) * (u ^ 2 * d.variance V) =
      -(N : ℝ) * ε ^ 2 * (d.variance V + B * ε) /
        (2 * d.variance V + B * ε) ^ 2 := by
    dsimp [u, D]
    have hne : 2 * d.variance V + B * ε ≠ 0 := ne_of_gt hD
    field_simp; ring
  rw [heq] at h
  exact h

/-- Explicit variance-sensitive exponential tail specialized to the source's
nonnegative finite vector and its supremum norm. -/
theorem empiricalRow_variance_tail_norm (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hV : ∀ s, 0 ≤ V s)
    (hnorm : 0 < ‖V‖) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 * (d.variance V + ‖V‖ * ε) /
        (2 * d.variance V + ‖V‖ * ε) ^ 2) := by
  apply d.empiricalRow_variance_tail_explicit V N hN ‖V‖ ε hnorm hε
  intro s
  exact ⟨hV s, (le_abs_self (V s)).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)⟩

end StatisticalRL.FiniteDistribution
