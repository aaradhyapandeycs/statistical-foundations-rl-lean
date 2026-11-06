import Formalization.Probability.EmpiricalBernsteinSharp.SelfBoundRatioSign
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Private uncompiled analytic comparison for the self-bounding Laplace
differential inequality. It is independent of any probability model. -/
open Filter Set
open scoped Topology
namespace StatisticalRL.EmpiricalBernsteinEntropy

/-- Two negative differentiable functions with a common negative initial
slope obey the comparison implied by the corresponding differential signs. -/
theorem negative_ratio_differential_comparison (H F Hd Fd D : ℝ → ℝ) (m : ℝ)
    (hm : 0 < m) (hH0 : H 0 = 0) (hF0 : F 0 = 0)
    (hHderiv0 : HasDerivAt H (-m) 0) (hFderiv0 : HasDerivAt F (-m) 0)
    (hHderiv : ∀ x, 0 < x → HasDerivAt H (Hd x) x)
    (hFderiv : ∀ x, 0 < x → HasDerivAt F (Fd x) x)
    (hD : ∀ x, 0 < x → 0 < D x)
    (hH : ∀ x, 0 < x → H x ≤ 0) (hF : ∀ x, 0 < x → F x < 0)
    (hHdiff : ∀ x, 0 < x → D x*Hd x ≤ H x)
    (hFdiff : ∀ x, 0 < x → F x ≤ D x*Fd x) :
    ∀ x, 0 ≤ x → H x ≤ F x := by
  let R : ℝ → ℝ := fun x ↦ H x/F x
  let Rd : ℝ → ℝ := fun x ↦ (Hd x*F x-H x*Fd x)/(F x)^2
  have hrderiv (x : ℝ) (hx : 0 < x) : HasDerivAt R (Rd x) x ∧ 0 ≤ Rd x :=
    ratio_has_nonnegative_derivative H F x (Hd x) (Fd x) (D x)
      (hHderiv x hx) (hFderiv x hx) (hD x hx) (hH x hx) (hF x hx)
      (hHdiff x hx) (hFdiff x hx)
  have hcont : ContinuousOn R (Ioi 0) := by
    intro x hx
    exact (hrderiv x hx).1.continuousAt.continuousWithinAt
  have hmono : MonotoneOn R (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0) hcont
    · intro x hx
      have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
      exact (hrderiv x hx').1.hasDerivWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
      exact (hrderiv x hx').2
  have hHslope : Tendsto (fun x : ℝ ↦ x⁻¹*H x) (𝓝[>] 0) (𝓝 (-m)) := by
    simpa only [zero_add, hH0, sub_zero, smul_eq_mul] using hHderiv0.tendsto_slope_zero_right
  have hFslope : Tendsto (fun x : ℝ ↦ x⁻¹*F x) (𝓝[>] 0) (𝓝 (-m)) := by
    simpa only [zero_add, hF0, sub_zero, smul_eq_mul] using hFderiv0.tendsto_slope_zero_right
  have hratio : Tendsto R (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have ht := hHslope.div hFslope (by linarith : -m ≠ 0)
    have heq : (fun x : ℝ ↦ (x⁻¹*H x)/(x⁻¹*F x)) =ᶠ[𝓝[>] 0] R := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      dsimp [R]
      field_simp [ne_of_gt hx', ne_of_lt (hF x hx')]
    have hlim := ht.congr' heq
    simpa only [div_self (by linarith : -m ≠ 0)] using hlim
  intro x hx
  rcases hx.eq_or_lt with rfl | hx
  · simp [hH0, hF0]
  · have hbound : 1 ≤ R x := by
      apply le_of_tendsto hratio
      have hxnear : Iio x ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds hx)
      filter_upwards [self_mem_nhdsWithin, hxnear] with y hy hyx
      exact hmono hy hx hyx.le
    dsimp [R] at hbound
    have := (le_div_iff_of_neg (hF x hx)).1 hbound
    linarith

end StatisticalRL.EmpiricalBernsteinEntropy
