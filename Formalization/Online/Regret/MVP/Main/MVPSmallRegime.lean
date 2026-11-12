import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Conditional deterministic small-regime arithmetic; no probability claim. -/
namespace StatisticalRL.OnlineRL

theorem mvp_main_small_regime_rate (d H K I R : ℝ)
    (hd : 1 ≤ d) (hH : 1 ≤ H) (hK : 0 ≤ K) (hI : 1 ≤ I)
    (hsmall : K ≤ d*I) (hreg : R ≤ K*H) :
    R ≤ 100*I*min (K*H) (Real.sqrt (d*K*H^2)) := by
  have hd0 : 0≤d := by linarith
  have hH0 : 0≤H := by linarith
  have hI0 : 0≤I := by linarith
  have hroot : 0≤Real.sqrt (d*K*H^2) := Real.sqrt_nonneg _
  have hscale : K*H ≤ I*Real.sqrt (d*K*H^2) := by
    have hs := Real.sq_sqrt (show 0≤d*K*H^2 by positivity)
    have hI2 : I≤I^2 := by nlinarith
    have hm := mul_nonneg (sub_nonneg.mpr hsmall) (show 0≤K*H^2 by positivity)
    have hm2 := mul_nonneg (sub_nonneg.mpr hI2) (show 0≤d*K*H^2 by positivity)
    have hsq : (I*Real.sqrt (d*K*H^2))^2 = I^2*(d*K*H^2) := by rw [mul_pow, hs]
    have hp : 0≤I*Real.sqrt (d*K*H^2) := mul_nonneg hI0 hroot
    have hk : 0≤K*H := mul_nonneg hK hH0
    nlinarith only [hm, hm2, hsq, hp, hk]
  have hKH : 0≤K*H := by positivity
  rcases le_total (K*H) (Real.sqrt (d*K*H^2)) with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hI) hKH]
  · rw [min_eq_right h]
    nlinarith

end StatisticalRL.OnlineRL
