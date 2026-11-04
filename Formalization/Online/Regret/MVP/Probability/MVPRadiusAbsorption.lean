import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Deterministic passage from peeled aggregate radius to source-shaped bound. -/
namespace StatisticalRL.OnlineRL

theorem mvp_radius_absorb (d x I n H L V floor : ℝ)
    (hd : 0 ≤ d) (hx : 0 < x) (hI : 0 ≤ I) (hn : 0 < n)
    (hH : 0 ≤ H) (hL : 1 ≤ L) (hV : 0 ≤ V)
    (hfloor : floor ≤ H^2) (hbudget : 32*L*x ≤ d*I) :
    (Real.sqrt (8 * max (n*V) floor * L) + (4/3)*H*L) / n ≤
      Real.sqrt (d*I*V/(4*n*x)) + d*H*I/(4*n*x) := by
  have hL0 : 0 ≤ L := by linarith
  have htarget : 0 ≤ d*I*V/(4*n*x) := by positivity
  have hsqrt : (Real.sqrt (d*I*V/(4*n*x)))^2 = d*I*V/(4*n*x) := Real.sq_sqrt htarget
  have hsquare : 8*n*V*L ≤ (n*Real.sqrt (d*I*V/(4*n*x)))^2 := by
    rw [mul_pow, hsqrt]
    have hm := mul_le_mul_of_nonneg_right hbudget (show 0 ≤ n*V by positivity)
    field_simp
    <;> nlinarith only [hm, hn, hx]
  have hrootVar : Real.sqrt (8*n*V*L) ≤ n*Real.sqrt (d*I*V/(4*n*x)) :=
    (Real.sqrt_le_left (by positivity)).2 hsquare
  have hrootFloor : Real.sqrt (8*H^2*L) ≤ 3*H*L := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith only [hH, hL, mul_nonneg (sq_nonneg H) (show 0 ≤ L*(L-1) by nlinarith)]
  have hroot : Real.sqrt (8*max (n*V) floor*L) ≤
      n*Real.sqrt (d*I*V/(4*n*x)) + 3*H*L := by
    rcases le_total floor (n*V) with h | h
    · rw [max_eq_left h]
      have hpos : 0 ≤ H*L := mul_nonneg hH hL0
      have hr : Real.sqrt (8*(n*V)*L) ≤ n*Real.sqrt (d*I*V/(4*n*x)) := by
        simpa only [mul_assoc] using hrootVar
      nlinarith only [hr, hpos]
    · rw [max_eq_right h]
      have hh : Real.sqrt (8*floor*L) ≤ Real.sqrt (8*H^2*L) := by
        apply Real.sqrt_le_sqrt
        nlinarith only [mul_nonneg hL0 (sub_nonneg.mpr hfloor)]
      have hpos : 0 ≤ n*Real.sqrt (d*I*V/(4*n*x)) := by positivity
      nlinarith only [hh, hrootFloor, hpos]
  have hlin : (13/3:ℝ)*H*L ≤ n*(d*H*I/(4*n*x)) := by
    have hm := mul_le_mul_of_nonneg_right hbudget hH
    field_simp
    <;> nlinarith only [hm, mul_nonneg hH (mul_nonneg hL0 hx.le)]
  apply (div_le_iff₀ hn).2
  nlinarith only [hroot, hlin]
end StatisticalRL.OnlineRL
