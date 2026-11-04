import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.Finset.Max

/-! strict-tail conversion on a finite sample space.
An actual sub-Gaussian MGF must be established before applying this helper. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem HasSubgaussianMGF.measure_gt_lt_of_finite
    {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hX : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε < X ω} < Real.exp (-ε^2 / (2 * c)) := by
  classical
  let bad : Finset Ω := Finset.univ.filter (fun ω => ε < X ω)
  by_cases hb : bad.Nonempty
  · obtain ⟨ω₀, hω₀, hmin⟩ := Finset.exists_min_image bad X hb
    have hε₀ : ε < X ω₀ := (Finset.mem_filter.mp hω₀).2
    have hsub : {ω | ε < X ω} ⊆ {ω | X ω₀ ≤ X ω} := by
      intro ω hω
      exact hmin ω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩)
    have hm := measureReal_mono hsub (measure_ne_top μ _)
    have ht := hX.measure_ge_le (show 0 ≤ X ω₀ by linarith)
    have hsq : ε^2 < (X ω₀)^2 := by
      have hp : 0 < (X ω₀ - ε) * (X ω₀ + ε) :=
        mul_pos (sub_pos.mpr hε₀) (by linarith)
      nlinarith
    have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
    have he : -(X ω₀)^2 / (2 * (c : ℝ)) < -ε^2 / (2 * (c : ℝ)) :=
      div_lt_div_of_pos_right (neg_lt_neg hsq) (by positivity)
    exact (hm.trans ht).trans_lt (Real.exp_lt_exp.mpr he)
  · have he : {ω | ε < X ω} = (∅ : Set Ω) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      apply hb
      exact ⟨ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩⟩
    rw [he, measureReal_empty]
    exact Real.exp_pos _

end StatisticalRL
