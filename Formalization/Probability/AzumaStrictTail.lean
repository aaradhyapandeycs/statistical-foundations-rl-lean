import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! strict general-space sub-Gaussian upper tail. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem azuma_subgaussian_strict_upper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (c : ℝ≥0) (hc : 0<c)
    (hX : HasSubgaussianMGF X c μ) (r : ℝ) (hr : 0<r) :
    μ.real {ω | r<X ω} < Real.exp (-r^2/(2*(c:ℝ))) := by
  classical
  have hc' : 0<(c:ℝ) := by exact_mod_cast hc
  let t : ℝ := r/(c:ℝ)
  have ht : 0<t := by dsimp [t]; positivity
  let A : Set Ω := {ω | r<X ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hXmeas
  let f : Ω → ℝ := fun ω => Real.exp (t*X ω) - A.indicator (fun _ => Real.exp (t*r)) ω
  have hEi : Integrable (fun ω => Real.exp (t*X ω)) μ := hX.integrable_exp_mul t
  have hIi : Integrable (A.indicator (fun _ => Real.exp (t*r))) μ :=
    (integrable_const (c := Real.exp (t*r))).indicator hA
  have hfi : Integrable f μ := hEi.sub hIi
  have hfpos : ∀ ω, 0<f ω := by
    intro ω
    by_cases hω : ω∈A
    · have hx : r<X ω := hω
      have he : Real.exp (t*r)<Real.exp (t*X ω) := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hx ht)
      simp only [f, Set.indicator_of_mem hω]
      linarith
    · simp only [f, Set.indicator_of_notMem hω, sub_zero]
      exact Real.exp_pos _
  have hsupport : Function.support f = Set.univ := by
    ext ω
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ne_of_gt (hfpos ω))
  have hpos : 0 < ∫ ω, f ω ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun ω => (hfpos ω).le) hfi).2
    rw [hsupport]
    simp
  have hint : (∫ ω, f ω ∂μ) = (∫ ω, Real.exp (t*X ω) ∂μ) - μ.real A*Real.exp (t*r) := by
    dsimp [f]
    rw [integral_sub hEi hIi, integral_indicator_const _ hA]
    simp only [smul_eq_mul]
  have hmgf : (∫ ω, Real.exp (t*X ω) ∂μ) ≤ Real.exp ((c:ℝ)*t^2/2) := by
    simpa only [ProbabilityTheory.mgf] using hX.mgf_le t
  have hmul : μ.real A*Real.exp (t*r) < Real.exp ((c:ℝ)*t^2/2) := by linarith
  have hdiv : μ.real A < Real.exp ((c:ℝ)*t^2/2) / Real.exp (t*r) :=
    (lt_div_iff₀ (Real.exp_pos _)).2 hmul
  rw [← Real.exp_sub] at hdiv
  have hexp : (c:ℝ)*t^2/2-t*r = -r^2/(2*(c:ℝ)) := by
    dsimp [t]
    field_simp
    ring
  simpa only [A,hexp] using hdiv
end StatisticalRL
