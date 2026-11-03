import Formalization.Probability.BernsteinExponentialEnvelope
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! A bounded-increment conditional Bernstein MGF ingredient.
This does not assert a martingale tail inequality. -/
open MeasureTheory
namespace StatisticalRL

/-- Conditional mean-zero bounded increments have a variance-sensitive
conditional exponential bound in the tuning range |t|B<3.
Integrability of all functions is derived from boundedness and measurability. -/
theorem conditional_mgf_le_exp_bernstein_secondMoment
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (X : Ω → ℝ)
    (hX : @Measurable Ω ℝ m₀ _ X) (B t : ℝ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B) (ht : |t| * B < 3)
    (hmean : μ[X | m] =ᵐ[μ] fun _ ↦ 0) :
    μ[fun ω ↦ Real.exp (t * X ω) | m] ≤ᵐ[μ]
      fun ω ↦ Real.exp ((t ^ 2 / (2 * (1 - |t| * B / 3))) *
        μ[fun ω' ↦ X ω' ^ 2 | m] ω) := by
  let c := t ^ 2 / (2 * (1 - |t| * B / 3))
  have hsmall : ∀ᵐ ω ∂μ, |t * X ω| ≤ |t| * B := by
    filter_upwards [hbound] with ω hω
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hω (abs_nonneg t)
  have hXi : Integrable X μ := Integrable.of_bound hX.aestronglyMeasurable B
    (by simpa only [Real.norm_eq_abs] using hbound)
  have hX2i : Integrable (fun ω ↦ X ω ^ 2) μ := by
    apply Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (B ^ 2)
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (X ω), mul_self_le_mul_self (abs_nonneg (X ω)) hω]
  have hei : Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
    apply Integrable.of_bound (by fun_prop) (Real.exp (|t| * B))
    filter_upwards [hsmall] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hω)
  have hpi : Integrable (fun ω ↦ 1 + t * X ω + c * X ω ^ 2) μ :=
    ((integrable_const 1).add (hXi.const_mul t)).add (hX2i.const_mul c)
  have hp : (fun ω ↦ Real.exp (t * X ω)) ≤ᵐ[μ]
      (fun ω ↦ 1 + t * X ω + c * X ω ^ 2) := by
    filter_upwards [hsmall] with ω hω
    have he := exp_le_one_add_add_bernstein_of_abs_le (t * X ω) (|t| * B) hω ht
    convert he using 1
    dsimp [c]
    ring

  have hc := condExp_mono hei hpi hp (m := m)
  have ha := condExp_add (integrable_const (1 : ℝ)) (hXi.const_mul t) m
  have hb := condExp_add ((integrable_const (1 : ℝ)).add (hXi.const_mul t))
    (hX2i.const_mul c) m
  have hs := condExp_smul (μ := μ) t X m
  have hs2 := condExp_smul (μ := μ) c (fun ω ↦ X ω ^ 2) m
  filter_upwards [hc, ha, hb, hs, hs2, hmean] with ω hc ha hb hs hs2 hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const hm] at *
  have hce : μ[fun ω ↦ 1 + t * X ω + c * X ω ^ 2 | m] ω =
      1 + c * μ[fun ω' ↦ X ω' ^ 2 | m] ω := by
    change μ[fun ω ↦ 1 + t * X ω + c * X ω ^ 2 | m] ω =
      μ[fun ω ↦ 1 + t * X ω | m] ω + μ[fun ω ↦ c * X ω ^ 2 | m] ω at hb
    change μ[fun ω ↦ 1 + t * X ω | m] ω = 1 + μ[fun ω ↦ t * X ω | m] ω at ha
    change μ[fun ω ↦ t * X ω | m] ω = t * μ[X | m] ω at hs
    change μ[fun ω ↦ c * X ω ^ 2 | m] ω = c * μ[fun ω ↦ X ω ^ 2 | m] ω at hs2
    rw [hb, ha, hs, hs2, hz]
    ring
  rw [hce] at hc
  have hex := Real.add_one_le_exp (c * μ[fun ω' ↦ X ω' ^ 2 | m] ω)
  exact hc.trans (by linarith)

end StatisticalRL
