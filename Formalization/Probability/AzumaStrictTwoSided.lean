import Formalization.Probability.AzumaStrictTail

/-! general-space strict two-sided sub-Gaussian source radius. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem azuma_subgaussian_strict_two_sided
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXm : Measurable X) (c : ℝ≥0) (hc : 0<c)
    (hX : HasSubgaussianMGF X c μ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1) :
    1-δ < μ.real {ω | |X ω| ≤ Real.sqrt (2*(c:ℝ)*Real.log (2/δ))} := by
  let ε := δ/2
  have hε : 0<ε := by dsimp [ε]; linarith
  have hε1 : ε<1 := by dsimp [ε]; linarith
  have hc' : 0<(c:ℝ) := by exact_mod_cast hc
  have hlog : 0<Real.log (1/ε) := Real.log_pos ((lt_div_iff₀ hε).2 (by linarith))
  let r := Real.sqrt (2*(c:ℝ)*Real.log (1/ε))
  have hr : 0<r := Real.sqrt_pos.mpr (by positivity)
  have he : Real.exp (-r^2/(2*(c:ℝ))) = ε := by
    dsimp [r]
    rw [Real.sq_sqrt (show 0≤2*(c:ℝ)*Real.log (1/ε) by positivity)]
    have heq : -(2*(c:ℝ)*Real.log (1/ε))/(2*(c:ℝ)) = -Real.log (1/ε) := by field_simp
    rw [heq, one_div, Real.log_inv, neg_neg, Real.exp_log hε]
  have hp := azuma_subgaussian_strict_upper μ X hXm c hc hX r hr
  have hn := azuma_subgaussian_strict_upper μ (-X) hXm.neg c hc hX.neg r hr
  rw [he] at hp hn
  let good : Set Ω := {ω | |X ω|≤r}
  have hg : MeasurableSet good := measurableSet_le hXm.abs measurable_const
  have hsub : goodᶜ ⊆ {ω | r<X ω} ∪ {ω | r<(-X) ω} := by
    intro ω hω
    have ha : r < |X ω| := lt_of_not_ge hω
    by_cases hx : 0≤X ω
    · left
      simpa only [Set.mem_setOf_eq, abs_of_nonneg hx] using ha
    · right
      simpa only [Set.mem_setOf_eq, Pi.neg_apply, abs_of_neg (lt_of_not_ge hx)] using ha
  have hbad : μ.real goodᶜ < 2*ε :=
    ((measureReal_mono hsub (measure_ne_top μ _)).trans (measureReal_union_le _ _)).trans_lt (by linarith)
  have hcompl := measureReal_add_measureReal_compl (μ := μ) hg
  rw [probReal_univ] at hcompl
  have hgood : 1-δ<μ.real good := by dsimp [ε] at hbad; linarith
  have hradius : r=Real.sqrt (2*(c:ℝ)*Real.log (2/δ)) := by
    dsimp [r,ε]
    congr 1
    congr 1
    congr 1
    field_simp
  simpa only [good,hradius] using hgood
end StatisticalRL
