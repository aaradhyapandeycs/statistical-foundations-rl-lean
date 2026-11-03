import Formalization.Probability.EmpiricalBernstein

/-! Sharp exponential-series estimates for bounded transition-row variables.
The statistical application concerns Lemma 2.5 of the source preliminaries. -/

open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.SharpBernstein

/-- The exponential remainder admits the variance-sensitive Bernstein majorant. -/
theorem exp_remainder_le (z : ℝ) (hz : |z| < 3) :
    Real.exp z ≤ 1 + z + z ^ 2 / (2 * (1 - |z| / 3)) := by
  have hr0 : 0 ≤ |z| / 3 := by positivity
  have hr1 : |z| / 3 < 1 := by linarith
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  have hmajor : Summable (fun n : ℕ ↦ (z ^ 2 / 2) * (|z| / 3) ^ n) :=
    hgeom.mul_left _
  have hseries : Summable (fun n : ℕ ↦ z ^ n / (n.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ℝ z).summable
  have htail : Summable (fun n : ℕ ↦ z ^ (n + 2) / ((n + 2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).2 hseries
  have hbound (n : ℕ) :
      z ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ (z ^ 2 / 2) * (|z| / 3) ^ n := by
    have hfacN : 2 * 3 ^ n ≤ (n + 2).factorial := by
      simpa [Nat.add_comm] using (Nat.factorial_mul_pow_le_factorial (m := 2) (n := n))
    have hfac : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by exact_mod_cast hfacN
    calc
      _ ≤ |z ^ (n + 2) / ((n + 2).factorial : ℝ)| := le_abs_self _
      _ = |z| ^ (n + 2) / ((n + 2).factorial : ℝ) := by
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ ((n + 2).factorial : ℝ))]
      _ ≤ |z| ^ (n + 2) / (2 * 3 ^ n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = (z ^ 2 / 2) * (|z| / 3) ^ n := by
        rw [pow_add, div_pow, sq_abs]
        ring
  have hsum := Summable.tsum_le_tsum hbound htail hmajor
  have hexp : (∑' n : ℕ, z ^ n / (n.factorial : ℝ)) = Real.exp z := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp ℝ z).tsum_eq
  have hsplit := hseries.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, pow_zero, pow_one, div_one, zero_add] at hsplit
  rw [hexp] at hsplit
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hsum
  rw [← div_eq_mul_inv] at hsum
  rw [← hsplit]
  have hden : 1 - |z| / 3 ≠ 0 := ne_of_gt (by linarith)
  convert add_le_add_left hsum (1 + z) using 1 <;> field_simp <;> ring

end StatisticalRL.SharpBernstein

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance sharpBernsteinStateMeasurable : MeasurableSpace State := ⊤

/-- Sharp Bernstein MGF bound for the actual centered transition-row law. -/
theorem centeredRow_mgf_le_sharp (d : FiniteDistribution State) (V : State → ℝ)
    (B u : ℝ) (hu : 0 ≤ u) (hsmall : u * B < 3)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u ≤
      Real.exp (u ^ 2 * d.variance V / (2 * (1 - u * B / 3))) := by
  have hμ0 : 0 ≤ d.expectation V := d.expectation_nonneg (fun s ↦ (hV s).1)
  have hμB : d.expectation V ≤ B := d.expectation_le_const (fun s ↦ (hV s).2)
  have hc (s : State) : |V s - d.expectation V| ≤ B := by
    apply abs_le.mpr
    constructor <;> linarith [(hV s).1, (hV s).2]
  have hden : 0 < 2 * (1 - u * B / 3) := by linarith
  have hpoint (s : State) :
      Real.exp (u * (V s - d.expectation V)) ≤
        1 + u * (V s - d.expectation V) +
          (u ^ 2 / (2 * (1 - u * B / 3))) * (V s - d.expectation V) ^ 2 := by
    have hz : |u * (V s - d.expectation V)| ≤ u * B := by
      rw [abs_mul, abs_of_nonneg hu]
      exact mul_le_mul_of_nonneg_left (hc s) hu
    have h3 : |u * (V s - d.expectation V)| < 3 := lt_of_le_of_lt hz hsmall
    have hcomp : (u * (V s - d.expectation V)) ^ 2 /
        (2 * (1 - |u * (V s - d.expectation V)| / 3)) ≤
        (u * (V s - d.expectation V)) ^ 2 / (2 * (1 - u * B / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) hden
      linarith
    have h := StatisticalRL.SharpBernstein.exp_remainder_le _ h3
    have heq : (u * (V s - d.expectation V)) ^ 2 / (2 * (1 - u * B / 3)) =
        (u ^ 2 / (2 * (1 - u * B / 3))) * (V s - d.expectation V) ^ 2 := by ring
    rw [heq] at hcomp
    linarith
  have hmean : d.expectation (fun s ↦ V s - d.expectation V) = 0 := by
    rw [d.expectation_sub, d.expectation_const, sub_self]
  calc
    ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u =
        d.expectation (fun s ↦ Real.exp (u * (V s - d.expectation V))) := by
      exact d.rowMeasure_integral _
    _ ≤ d.expectation (fun s ↦ 1 + u * (V s - d.expectation V) +
        (u ^ 2 / (2 * (1 - u * B / 3))) * (V s - d.expectation V) ^ 2) :=
      d.expectation_mono hpoint
    _ = 1 + u ^ 2 * d.variance V / (2 * (1 - u * B / 3)) := by
      rw [d.expectation_add, d.expectation_add, d.expectation_const,
        d.expectation_mul, d.expectation_mul, hmean,
        ← d.variance_eq_expectation_centered_sq]
      ring
    _ ≤ Real.exp (u ^ 2 * d.variance V / (2 * (1 - u * B / 3))) := by
      linarith [Real.add_one_le_exp (u ^ 2 * d.variance V / (2 * (1 - u * B / 3)))]

/-- Sharp Chernoff inequality for the actual iid empirical row, before tuning. -/
theorem empiricalRow_upper_sharp_chernoff (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε u : ℝ) (hu : 0 ≤ u) (hsmall : u * B < 3)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} ≤
      Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) *
        (u ^ 2 * d.variance V / (2 * (1 - u * B / 3)))) := by
  have hmgf := d.centeredRow_mgf_le_sharp V B u hu hsmall hV
  have hnonneg : 0 ≤ ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u :=
    ProbabilityTheory.mgf_nonneg
  calc
    _ ≤ Real.exp (-u * ((N : ℝ) * ε)) *
        (ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u) ^ N :=
      d.empiricalRow_chernoff_mgf V N hN ε u hu
    _ ≤ Real.exp (-u * ((N : ℝ) * ε)) *
        (Real.exp (u ^ 2 * d.variance V / (2 * (1 - u * B / 3)))) ^ N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hmgf N) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

/-- Optimizing the sharp Chernoff bound gives the classical Bernstein exponent
for positive row variance; this is the actual iid sampling law. -/
theorem empiricalRow_upper_sharp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hvar : 0 < d.variance V) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} ≤
      Real.exp (-(N : ℝ) * ε ^ 2 / (2 * (d.variance V + B * ε / 3))) := by
  let D : ℝ := d.variance V + B * ε / 3
  have hD : 0 < D := by dsimp [D]; positivity
  let u : ℝ := ε / D
  have hu : 0 ≤ u := div_nonneg hε hD.le
  have hsmall : u * B < 3 := by
    dsimp [u]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    dsimp [D]
    linarith
  have h := d.empiricalRow_upper_sharp_chernoff V N hN B ε u hu hsmall hV
  have heq : -u * ((N : ℝ) * ε) + (N : ℝ) *
      (u ^ 2 * d.variance V / (2 * (1 - u * B / 3))) =
      -(N : ℝ) * ε ^ 2 / (2 * (d.variance V + B * ε / 3)) := by
    have hvarne : d.variance V ≠ 0 := ne_of_gt hvar
    have hDne : D ≠ 0 := ne_of_gt hD
    dsimp [u]
    have hden : 1 - ε / D * B / 3 ≠ 0 := by
      apply ne_of_gt
      have := hsmall
      dsimp [u] at this
      linarith
    dsimp [D] at *
    field_simp
    ring
  rwa [heq] at h

/-- Lower tail by reflection, with no positivity requirement on the policy support. -/
theorem empiricalRow_lower_sharp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hvar : 0 < d.variance V) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ -((empiricalRow N hN ω).expectation V - d.expectation V)} ≤
      Real.exp (-(N : ℝ) * ε ^ 2 / (2 * (d.variance V + B * ε / 3))) := by
  let W : State → ℝ := fun s ↦ B - V s
  have hw (s : State) : W s ∈ Set.Icc 0 B := by
    dsimp [W]
    constructor <;> linarith [(hV s).1, (hV s).2]
  have hv : d.variance W = d.variance V := d.variance_const_sub V B
  have h := d.empiricalRow_upper_sharp W N hN B ε hB hε (by rwa [hv]) hw
  rw [hv] at h
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

/-- Two-sided Bernstein tail for actual iid row samples, for positive variance. -/
theorem empiricalRow_twoSided_sharp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hvar : 0 < d.variance V) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / (2 * (d.variance V + B * ε / 3))) := by
  let D : (Fin N → State) → ℝ := fun ω ↦ (empiricalRow N hN ω).expectation V - d.expectation V
  have hp := d.empiricalRow_upper_sharp V N hN B ε hB hε hvar hV
  have hn := d.empiricalRow_lower_sharp V N hN B ε hB hε hvar hV
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
    _ ≤ 2 * Real.exp (-(N : ℝ) * ε ^ 2 / (2 * (d.variance V + B * ε / 3))) := by
      simpa only [two_mul] using add_le_add hp hn

/-- Positive deviations are impossible when the row variance vanishes. -/
theorem empiricalRow_zeroVariance_sharp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hvar : d.variance V = 0) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} = 0 := by
  rw [measureReal_def, d.empiricalRow_zeroVariance_tail V N hN ε hε hvar]
  simp

/-- Source-constant threshold for one deterministic vector and positive row variance. -/
theorem empiricalRow_source_threshold (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hvar : 0 < d.variance V) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2 * L * d.variance V / N) + 2 * B * L / (3 * N) ≤
        |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-L) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let x : ℝ := Real.sqrt (2 * L * d.variance V / N)
  let y : ℝ := 2 * B * L / (3 * N)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hnx : (N : ℝ) * x ^ 2 = 2 * L * d.variance V := by
    dsimp [x]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hny : (N : ℝ) * y = 2 * B * L / 3 := by
    dsimp [y]
    field_simp
  have h := d.empiricalRow_twoSided_sharp V N hN B (x + y) hB (add_nonneg hx hy) hvar hV
  have hden : 0 < 2 * (d.variance V + B * (x + y) / 3) := by positivity
  have hcross : 0 ≤ (N : ℝ) * x * y := by positivity
  have hny' := congrArg (fun t : ℝ ↦ t * (x + y)) hny
  have hexp : -(N : ℝ) * (x + y) ^ 2 /
      (2 * (d.variance V + B * (x + y) / 3)) ≤ -L := by
    rw [div_le_iff₀ hden]
    nlinarith [hnx, hny', hcross]
  calc
    _ ≤ 2 * Real.exp (-(N : ℝ) * (x + y) ^ 2 /
        (2 * (d.variance V + B * (x + y) / 3))) := h
    _ ≤ 2 * Real.exp (-L) := by gcongr

/-- The strict failure event obeys the source-constant threshold, including
zero variance and zero range. -/
theorem empiricalRow_source_threshold_strict (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B L : ℝ) (hB : 0 ≤ B) (hL : 0 < L)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2 * L * d.variance V / N) + 2 * B * L / (3 * N) <
        |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-L) := by
  let t : ℝ := Real.sqrt (2 * L * d.variance V / N) + 2 * B * L / (3 * N)
  by_cases hv : 0 < d.variance V
  · have h := d.empiricalRow_source_threshold V N hN B L hB hL.le hv hV
    calc
      (d.sampleMeasure N).real {ω | t < |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
          (d.sampleMeasure N).real {ω | t ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} := by
        apply measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        exact le_of_lt (show t < |(empiricalRow N hN ω).expectation V - d.expectation V| from hω)
      _ ≤ 2 * Real.exp (-L) := h
  · have hv0 : d.variance V = 0 := le_antisymm (le_of_not_gt hv) (d.variance_nonneg V)
    by_cases hB0 : B = 0
    · have hzero : V = fun _ ↦ 0 := by
        funext s
        have hs := hV s
        rw [hB0] at hs
        exact le_antisymm hs.2 hs.1
      subst V
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hempty : {ω : Fin N → State | t <
          |(empiricalRow N hN ω).expectation (fun _ ↦ 0) - d.expectation (fun _ ↦ 0)|} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [FiniteDistribution.expectation_const, FiniteDistribution.expectation_const]
        simp only [sub_self, abs_zero]
        exact not_lt_of_ge ht
      rw [hempty, measureReal_empty]
      positivity
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      have ht : 0 < t := by
        dsimp [t]
        have hn : (0 : ℝ) < N := by exact_mod_cast hN
        positivity
      have hz := d.empiricalRow_zeroVariance_sharp V N hN t ht hv0
      have hm : (d.sampleMeasure N).real {ω | t <
          |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤ 0 := by
        calc
          _ ≤ (d.sampleMeasure N).real {ω | t ≤
              |(empiricalRow N hN ω).expectation V - d.expectation V|} := by
            apply measureReal_mono ?_ (measure_ne_top _ _)
            intro ω hω
            exact le_of_lt (show t < |(empiricalRow N hN ω).expectation V - d.expectation V| from hω)
          _ = 0 := hz
      exact hm.trans (by positivity)

end StatisticalRL.FiniteDistribution
