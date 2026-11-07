import Formalization.Probability.AzumaSumMGF
import Formalization.Probability.AzumaStrictTwoSided
import Formalization.Probability.AzumaScalarChord

/-!
# Azuma–Hoeffding for an arbitrary filtration (strict two-sided form)

`lem:azuma-hoeffding` (`chapters/prelim.tex:1038–1054`) in the form used by the LCB-Q analysis:
increments `X i` that are measurable at time `i+1`, centred given `ℱ i`, and bounded by
deterministic `B i`. For `0 < δ < 1`,
`1 − δ < P(|Σ_{i<n} X_i| ≤ √(2 Σ_{i<n} B_i² log(2/δ)))`.
The proof composes `azuma_sum_mgf_bound` and `azuma_subgaussian_strict_two_sided`, exactly as
`azuma_natural_history_source` does for the natural filtration.
-/

namespace StatisticalRL

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem azuma_filtration_strict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (B : ℕ → ℝ) (hX : ∀ i, Measurable (X i))
    (hb : ∀ i ω, |X i ω| ≤ B i)
    (hc : ∀ i, μ[X i | ℱ i] =ᵐ[μ] 0)
    (hadapt : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < μ.real {ω | |∑ i ∈ Finset.range n, X i ω| ≤
      Real.sqrt (2 * (∑ i ∈ Finset.range n, (B i) ^ 2) * Real.log (2 / δ))} := by
  classical
  have hne : Nonempty Ω := by
    by_contra h
    have hzero : μ Set.univ = 0 := by
      rw [Set.univ_eq_empty_iff.mpr (not_nonempty_iff.mp h), measure_empty]
    rw [measure_univ] at hzero
    exact zero_ne_one hzero.symm
  obtain ⟨ω₀⟩ := hne
  have hB : ∀ i, 0 ≤ B i := fun i => le_trans (abs_nonneg _) (hb i ω₀)
  have hSm : ∀ j, StronglyMeasurable[ℱ j] (fun ω => ∑ i ∈ Finset.range j, X i ω) := by
    intro j
    have hsum : StronglyMeasurable[ℱ j] (∑ i ∈ Finset.range j, X i) := by
      apply Finset.stronglyMeasurable_sum
      intro i hi
      have hij : i + 1 ≤ j := by have := Finset.mem_range.mp hi; omega
      exact (hadapt i).mono (ℱ.mono hij)
    convert hsum using 1
    funext ω
    simp only [Finset.sum_apply]
  let Y : Ω → ℝ := fun ω => ∑ i ∈ Finset.range n, X i ω
  let c : ℝ≥0 := ∑ i ∈ Finset.range n, ⟨(B i) ^ 2, sq_nonneg _⟩
  have hcval : (c : ℝ) = ∑ i ∈ Finset.range n, (B i) ^ 2 := by simp [c]
  have hYm : Measurable Y := Finset.measurable_sum _ (fun i _ => hX i)
  have hYbound : ∀ ω, |Y ω| ≤ ∑ i ∈ Finset.range n, B i := by
    intro ω
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hb i ω))
  have hYIcc : ∀ ω, Y ω ∈ Set.Icc (-(∑ i ∈ Finset.range n, B i)) (∑ i ∈ Finset.range n, B i) :=
    fun ω => abs_le.mp (hYbound ω)
  have hmgf : HasSubgaussianMGF Y c μ := by
    constructor
    · intro t
      exact integrable_exp_mul_of_mem_Icc hYm.aemeasurable (Filter.Eventually.of_forall hYIcc)
    · intro t
      simpa only [ProbabilityTheory.mgf, Y, hcval, mul_comm] using
        azuma_sum_mgf_bound μ ℱ X B hX hB hb hc hSm n t
  by_cases hcp : 0 < c
  · have h := azuma_subgaussian_strict_two_sided μ Y hYm c hcp hmgf δ hδ hδ1
    simpa only [Y, hcval] using h
  · have hc0 : c = 0 := le_antisymm (le_of_not_gt hcp) (zero_le c)
    have hsum0 : (∑ i ∈ Finset.range n, (B i) ^ 2) = 0 := by
      simpa [hcval] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hc0
    have hzeros : ∀ i ∈ Finset.range n, B i = 0 := by
      intro i hi
      have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (B i))).1 hsum0 i hi
      exact sq_eq_zero_iff.mp hs
    have hYzero : Y = 0 := by
      funext ω
      dsimp [Y]
      apply Finset.sum_eq_zero
      intro i hi
      have hx := hb i ω
      rw [hzeros i hi] at hx
      exact azuma_zero_width (X i ω) hx
    have hgood : {ω | |Y ω| ≤ Real.sqrt (2 * (∑ i ∈ Finset.range n, (B i) ^ 2) *
        Real.log (2 / δ))} = Set.univ := by
      ext ω
      simp [hYzero, hsum0]
    change 1 - δ < μ.real {ω | |Y ω| ≤ Real.sqrt (2 * (∑ i ∈ Finset.range n, (B i) ^ 2) *
      Real.log (2 / δ))}
    rw [hgood, probReal_univ]
    linarith

end StatisticalRL
