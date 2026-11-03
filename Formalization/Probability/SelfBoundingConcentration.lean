import Formalization.Probability.EmpiricalVarianceBernstein

/-! A weaker exponential lower tail for actual empirical standard deviation,
proved by centered moments. No entropy or self-bounding tail is assumed. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance selfBoundingStateMeasurable : MeasurableSpace State := ⊤

/-- The squared centered vector is bounded by the original range squared. -/
theorem centeredSquare_mem_Icc (d : FiniteDistribution State) (V : State → ℝ)
    (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B) (s : State) :
    (V s - d.expectation V) ^ 2 ∈ Set.Icc 0 (B ^ 2) := by
  have hm0 := d.expectation_nonneg (fun s ↦ (hV s).1)
  have hmB := d.expectation_le_const (fun s ↦ (hV s).2)
  constructor
  · positivity
  · have hp : 0 ≤ (B - V s + d.expectation V) * (B + V s - d.expectation V) :=
      mul_nonneg (by linarith [(hV s).2]) (by linarith [(hV s).1])
    nlinarith

/-- Centered-square variance retains population-variance dependence. -/
theorem centeredSquare_variance_le (d : FiniteDistribution State) (V : State → ℝ)
    (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    d.variance (fun s ↦ (V s - d.expectation V) ^ 2) ≤ B ^ 2 * d.variance V := by
  calc
    _ ≤ d.expectation (fun s ↦ ((V s - d.expectation V) ^ 2) ^ 2) :=
      d.variance_le_expectation_sq _
    _ ≤ d.expectation (fun s ↦ B ^ 2 * (V s - d.expectation V) ^ 2) := by
      apply d.expectation_mono
      intro s
      have h := d.centeredSquare_mem_Icc V B hV s
      nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
    _ = _ := by rw [d.expectation_mul, ← d.variance_eq_expectation_centered_sq]

/-- Exact recentering identity on each actual sample. -/
theorem empiricalVariance_eq_centeredSquare_sub (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (V : State → ℝ) (ω : Fin N → State) :
    empiricalVariance N hN V ω =
      (empiricalRow N hN ω).expectation (fun s ↦ (V s - d.expectation V) ^ 2) -
        ((empiricalRow N hN ω).expectation V - d.expectation V) ^ 2 := by
  have hexpand : (fun s ↦ (V s - d.expectation V) ^ 2) =
      (fun s ↦ V s ^ 2 - 2 * d.expectation V * V s + (d.expectation V) ^ 2) := by
    funext s
    ring
  rw [hexpand, expectation_add, expectation_sub, expectation_mul, expectation_const]
  unfold empiricalVariance variance
  ring

/-- Variance-sensitive lower tail for the centered-square empirical mean.
The restricted tuning parameter is explicit; no concentration is an input. -/
theorem centeredSquare_lower_tail (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B a u : ℝ) (hu : 0 ≤ u) (hsmall : u * B ^ 2 ≤ 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | a ≤ d.variance V -
      (empiricalRow N hN ω).expectation (fun s ↦ (V s - d.expectation V) ^ 2)} ≤
      Real.exp (-u * ((N : ℝ) * a) + (N : ℝ) * (u ^ 2 * (B ^ 2 * d.variance V))) := by
  have h := d.empiricalRow_lower_variance_tail (fun s ↦ (V s - d.expectation V) ^ 2)
    N hN (B ^ 2) a u hu hsmall (d.centeredSquare_mem_Icc V B hV)
  rw [← d.variance_eq_expectation_centered_sq] at h
  have heq : {ω | a ≤ -((empiricalRow N hN ω).expectation
      (fun s ↦ (V s - d.expectation V) ^ 2) - d.variance V)} =
      {ω | a ≤ d.variance V - (empiricalRow N hN ω).expectation
        (fun s ↦ (V s - d.expectation V) ^ 2)} := by
    ext ω
    simp only [Set.mem_setOf_eq, neg_sub]
  rw [heq] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hv := d.centeredSquare_variance_le V B hV
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_nonneg hn (mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hv))]

/-- An exponential lower tail for empirical standard deviation in the
nontrivial range t≤population standard deviation. Constants are not source sharp. -/
theorem empiricalStd_lower_tail_of_le (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B t : ℝ) (hB : 0 < B) (ht : 0 < t)
    (htσ : t ≤ Real.sqrt (d.variance V)) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | Real.sqrt (empiricalVariance N hN V ω) + t <
      Real.sqrt (d.variance V)} ≤
      Real.exp (-(N : ℝ) * t ^ 2 / (16 * B ^ 2)) +
        2 * Real.exp (-(N : ℝ) * t ^ 2 / B ^ 2) := by
  let σ := Real.sqrt (d.variance V)
  have hσ : 0 < σ := lt_of_lt_of_le ht htσ
  have hσsq : σ ^ 2 = d.variance V := Real.sq_sqrt (d.variance_nonneg V)
  let a := σ * t / 2
  let r := Real.sqrt a
  let u := t / (4 * B ^ 2 * σ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hrsq : r ^ 2 = a := Real.sq_sqrt ha.le
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsmall : u * B ^ 2 ≤ 1 := by
    dsimp [u]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 4 * B ^ 2 * σ)]
    have h := mul_le_mul_of_nonneg_left htσ (sq_nonneg B)
    nlinarith
  let A : Set (Fin N → State) := {ω | a ≤ d.variance V -
    (empiricalRow N hN ω).expectation (fun s ↦ (V s - d.expectation V) ^ 2)}
  let C : Set (Fin N → State) := {ω | r ≤
    |(empiricalRow N hN ω).expectation V - d.expectation V|}
  have hsubset : {ω | Real.sqrt (empiricalVariance N hN V ω) + t < σ} ⊆ A ∪ C := by
    intro ω hω
    by_contra hout
    have hA : d.variance V - (empiricalRow N hN ω).expectation
        (fun s ↦ (V s - d.expectation V) ^ 2) < a := by
      exact lt_of_not_ge (fun h ↦ hout (Set.mem_union_left C h))
    have hC : |(empiricalRow N hN ω).expectation V - d.expectation V| < r := by
      exact lt_of_not_ge (fun h ↦ hout (Set.mem_union_right A h))
    have hCsq : ((empiricalRow N hN ω).expectation V - d.expectation V) ^ 2 < a := by
      have hp := mul_pos (sub_pos.mpr hC)
        (add_pos_of_pos_of_nonneg (lt_of_le_of_lt (abs_nonneg _) hC) (abs_nonneg ((empiricalRow N hN ω).expectation V - d.expectation V)))
      nlinarith [sq_abs ((empiricalRow N hN ω).expectation V - d.expectation V)]
    have hzsq := Real.sq_sqrt (empiricalVariance_nonneg N hN V ω)
    have hz0 := Real.sqrt_nonneg (empiricalVariance N hN V ω)
    have hpos : 0 < σ - (Real.sqrt (empiricalVariance N hN V ω) + t) := sub_pos.mpr hω
    have hprod := mul_pos hpos (by linarith : 0 < σ - t +
      Real.sqrt (empiricalVariance N hN V ω))
    have hst := mul_nonneg ht.le (sub_nonneg.mpr htσ)
    have hid := d.empiricalVariance_eq_centeredSquare_sub N hN V ω
    dsimp [a] at hA hCsq
    nlinarith
  have hA := d.centeredSquare_lower_tail V N hN B a u hu hsmall hV
  have hC := d.empiricalRow_hoeffding V N hN B r hB hV (Real.sqrt_nonneg _)
  have heq : -u * ((N : ℝ) * a) + (N : ℝ) * (u ^ 2 * (B ^ 2 * d.variance V)) =
      -(N : ℝ) * t ^ 2 / (16 * B ^ 2) := by
    rw [← hσsq]
    dsimp [u, a]
    field_simp
    ring
  rw [heq] at hA
  have hC' : (d.sampleMeasure N).real C ≤ 2 * Real.exp (-(N : ℝ) * t ^ 2 / B ^ 2) := by
    refine hC.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
    rw [hrsq]
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hB)).2
    dsimp [a]
    have h := mul_nonneg (mul_nonneg hn ht.le) (sub_nonneg.mpr htσ)
    nlinarith
  calc
    _ ≤ (d.sampleMeasure N).real (A ∪ C) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ (d.sampleMeasure N).real A + (d.sampleMeasure N).real C := measureReal_union_le _ _
    _ ≤ _ := add_le_add hA hC'

/-- Exponential empirical-standard-deviation lower tail for every positive t.
The bound has the correct N-dependent scale but weaker constants than source. -/
theorem empiricalStd_lower_tail (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B t : ℝ) (hB : 0 < B) (ht : 0 < t)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | Real.sqrt (empiricalVariance N hN V ω) + t <
      Real.sqrt (d.variance V)} ≤ 3 * Real.exp (-(N : ℝ) * t ^ 2 / (16 * B ^ 2)) := by
  by_cases htσ : t ≤ Real.sqrt (d.variance V)
  · have h := d.empiricalStd_lower_tail_of_le V N hN B t hB ht htσ hV
    refine h.trans ?_
    have he : Real.exp (-(N : ℝ) * t ^ 2 / B ^ 2) ≤
        Real.exp (-(N : ℝ) * t ^ 2 / (16 * B ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
      apply (div_le_div_iff₀ hB2 (by positivity : 0 < 16 * B ^ 2)).2
      nlinarith [mul_nonneg (mul_nonneg hn (sq_nonneg t)) hB2.le]
    linarith
  · have hempty : {ω | Real.sqrt (empiricalVariance N hN V ω) + t <
        Real.sqrt (d.variance V)} = (∅ : Set (Fin N → State)) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      linarith [Real.sqrt_nonneg (empiricalVariance N hN V ω)]
    rw [hempty, measureReal_empty]
    positivity

/-- An explicit standard-deviation confidence radius, with failure at most 3e⁻ˣ.
This theorem does not assert the sharp empirical Bernstein mean-error radius. -/
theorem empiricalStd_lower_tail_exp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B x : ℝ) (hB : 0 < B) (hx : 0 < x)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | Real.sqrt (empiricalVariance N hN V ω) +
      4 * B * Real.sqrt (x / N) < Real.sqrt (d.variance V)} ≤ 3 * Real.exp (-x) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt (x / N) := Real.sqrt_pos.mpr (div_pos hx hn)
  have h := d.empiricalStd_lower_tail V N hN B (4 * B * Real.sqrt (x / N))
    hB (by positivity) hV
  have heq : -(N : ℝ) * (4 * B * Real.sqrt (x / N)) ^ 2 / (16 * B ^ 2) = -x := by
    have hsq := Real.sq_sqrt (div_pos hx hn).le
    rw [mul_pow, mul_pow, hsq]
    field_simp
    ring
  rwa [heq] at h

/-- Population standard deviation is at most empirical standard deviation
plus this computable radius, except on an event of probability at most δ. -/
theorem empiricalStd_lower_tail_confidence (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω | Real.sqrt (empiricalVariance N hN V ω) +
      4 * B * Real.sqrt (Real.log (3 / δ) / N) < Real.sqrt (d.variance V)} ≤ δ := by
  have hratio : 1 < 3 / δ := (lt_div_iff₀ hδ).2 (by linarith)
  have h := d.empiricalStd_lower_tail_exp V N hN B (Real.log (3 / δ)) hB
    (Real.log_pos hratio) hV
  have heq : 3 * Real.exp (-Real.log (3 / δ)) = δ := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 3 / δ)]
    field_simp
  rwa [heq] at h

end StatisticalRL.FiniteDistribution
