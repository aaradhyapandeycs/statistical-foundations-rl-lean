import Formalization.Probability.EmpiricalRow
import Mathlib.Probability.Moments.SubGaussian

/-! Fixed-vector Hoeffding prerequisites on the actual independent row sample law.
Source: arXiv:2610.41903v1, preliminaries, Lemma 2.4. -/

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance hoeffdingStateMeasurable : MeasurableSpace State := ⊤

/-- Centered evaluation of one actual sample. -/
def centeredSample (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (i : Fin N) (ω : Fin N → State) : ℝ :=
  V (ω i) - d.expectation V

/-- The centered sample family is independent under the actual product law. -/
theorem centeredSample_independent (d : FiniteDistribution State) (V : State → ℝ) (N : ℕ) :
    iIndepFun (d.centeredSample V N) (d.sampleMeasure N) := by
  exact (d.sampleMeasure_independent N).comp (fun _ x ↦ V x - d.expectation V)
    (fun _ ↦ measurable_of_countable _)

/-- Hoeffding's lemma applied to each actual centered sample. -/
theorem centeredSample_subgaussian (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (i : Fin N) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    HasSubgaussianMGF (d.centeredSample V N i) ((‖B‖₊ / 2) ^ 2) (d.sampleMeasure N) := by
  have hm : AEMeasurable (fun ω : Fin N → State ↦ V (ω i)) (d.sampleMeasure N) :=
    ((measurable_of_countable V).comp (measurable_pi_apply i)).aemeasurable
  have hb : ∀ᵐ ω ∂(d.sampleMeasure N), V (ω i) ∈ Set.Icc 0 B :=
    Filter.Eventually.of_forall (fun ω ↦ hV (ω i))
  have h := hasSubgaussianMGF_of_mem_Icc hm hb
  rw [d.sampleMeasure_coordinate_integral N i V] at h
  simpa only [centeredSample, sub_zero] using h

/-- The centered sum inherits the sharp variance-proxy sum by independence. -/
theorem centeredSum_subgaussian (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    HasSubgaussianMGF (fun ω ↦ ∑ i : Fin N, d.centeredSample V N i ω)
      ((N : ℝ≥0) * (‖B‖₊ / 2) ^ 2) (d.sampleMeasure N) := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun (d.centeredSample_independent V N)
    (s := Finset.univ) (c := fun _ ↦ (‖B‖₊ / 2) ^ 2)
    (fun i _ ↦ d.centeredSample_subgaussian V N i B hV)
  simpa using h

/-- A two-sided Hoeffding bound for the centered sum, with Mathlib's
finite-sample variance proxy. -/
theorem centeredSum_twoSided (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (B t : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B) (ht : 0 ≤ t) :
    (d.sampleMeasure N).real {ω | t ≤ |∑ i : Fin N, d.centeredSample V N i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((N : ℝ≥0) * (‖B‖₊ / 2) ^ 2 : ℝ≥0))) := by
  let S : (Fin N → State) → ℝ := fun ω ↦ ∑ i : Fin N, d.centeredSample V N i ω
  have hsg := d.centeredSum_subgaussian V N B hV
  change HasSubgaussianMGF S _ _ at hsg
  have hp := hsg.measure_ge_le ht
  have hn := hsg.neg.measure_ge_le ht
  calc
    (d.sampleMeasure N).real {ω | t ≤ |S ω|} ≤
        (d.sampleMeasure N).real ({ω | t ≤ S ω} ∪ {ω | t ≤ -S ω}) := by
          apply measureReal_mono ?_ (measure_ne_top _ _)
          intro ω hω
          change t ≤ |S ω| at hω
          change t ≤ S ω ∨ t ≤ -S ω
          exact (le_abs).mp hω
    _ ≤ (d.sampleMeasure N).real {ω | t ≤ S ω} +
        (d.sampleMeasure N).real {ω | t ≤ -S ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-t ^ 2 / (2 * ((N : ℝ≥0) * (‖B‖₊ / 2) ^ 2 : ℝ≥0))) := by
      simpa only [Pi.neg_apply, two_mul] using add_le_add hp hn

/-- The centered sum is exactly `N` times the empirical-row deviation. -/
theorem centeredSum_eq_empirical (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ω : Fin N → State) :
    (∑ i : Fin N, d.centeredSample V N i ω) =
      (N : ℝ) * ((empiricalRow N hN ω).expectation V - d.expectation V) := by
  rw [empiricalRow_expectation]
  simp only [centeredSample, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp

/-- Fixed-vector, two-sided Hoeffding tail with the source interval constant. -/
theorem empiricalRow_hoeffding (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B ε : ℝ) (hB : 0 < B)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) (hε : 0 ≤ ε) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-2 * (N : ℝ) * ε ^ 2 / B ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have htail := d.centeredSum_twoSided V N B ((N : ℝ) * ε) hV (mul_nonneg hn.le hε)
  have hset : {ω | (N : ℝ) * ε ≤ |∑ i : Fin N, d.centeredSample V N i ω|} =
      {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} := by
    ext ω
    change (N : ℝ) * ε ≤ |∑ i : Fin N, d.centeredSample V N i ω| ↔
      ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|
    rw [d.centeredSum_eq_empirical V N hN ω, abs_mul, abs_of_pos hn]
    exact mul_le_mul_iff_right₀ hn
  rw [hset] at htail
  have hden : (2 * ((N : ℝ≥0) * (‖B‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) =
      (N : ℝ) * B ^ 2 / 2 := by
    simp [Real.norm_eq_abs, abs_of_pos hB]
    ring
  have heq : -((N : ℝ) * ε) ^ 2 /
      (2 * ((N : ℝ≥0) * (‖B‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) =
      -2 * (N : ℝ) * ε ^ 2 / B ^ 2 := by
    rw [hden]
    have hN' : (N : ℝ) ≠ 0 := ne_of_gt hn
    have hB' : B ≠ 0 := ne_of_gt hB
    field_simp
  rw [heq] at htail
  exact htail

/-- The source's fixed nonnegative vector uses its finite supremum norm. -/
theorem empiricalRow_hoeffding_norm (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ s, 0 ≤ V s) (hnorm : 0 < ‖V‖) :
    (d.sampleMeasure N).real {ω | ε ≤ |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      2 * Real.exp (-2 * (N : ℝ) * ε ^ 2 / ‖V‖ ^ 2) := by
  apply d.empiricalRow_hoeffding V N hN ‖V‖ ε hnorm _ hε
  intro s
  exact ⟨hV s, (le_abs_self (V s)).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)⟩

/-- If the source vector's norm is zero then the actual deviation is zero. -/
theorem empiricalRow_norm_zero_deviation (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (hnorm : ‖V‖ = 0) (ω : Fin N → State) :
    (empiricalRow N hN ω).expectation V - d.expectation V = 0 := by
  have hzero : V = 0 := norm_eq_zero.mp hnorm
  rw [hzero]
  simp [expectation]

/-- In the degenerate interval `[0,0]`, every empirical deviation is zero. -/
theorem empiricalRow_zero_deviation (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (hV : ∀ s, V s ∈ Set.Icc 0 0) (ω : Fin N → State) :
    (empiricalRow N hN ω).expectation V - d.expectation V = 0 := by
  have hzero : V = 0 := by
    funext s
    exact le_antisymm (hV s).2 (hV s).1
  rw [hzero]
  simp [expectation]

end StatisticalRL.FiniteDistribution
