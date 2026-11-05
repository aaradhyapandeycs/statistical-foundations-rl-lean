import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Large-regime conversion to the min-rate expression. -/
namespace StatisticalRL.OnlineRL

theorem mvp_main_large_min_rate (d H K I R : ℝ)
    (hd : 1≤d) (hH : 1≤H) (hI : 1≤I) (hK : d*I≤K)
    (hreg : R≤100*Real.sqrt (d*K*H^2)*I) :
    R≤100*max 1 I*min (K*H) (Real.sqrt (d*K*H^2)) := by
  have hd0 : 0≤d := by linarith
  have hH0 : 0≤H := by linarith
  have hK0 : 0≤K := by nlinarith
  have hdk : d≤K := by nlinarith [mul_nonneg (sub_nonneg.mpr hI) hd0]
  have hroot : Real.sqrt (d*K*H^2) ≤ K*H := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr hdk) (show 0≤K*H^2 by positivity)]
  rw [max_eq_right hI, min_eq_right hroot]
  nlinarith
end StatisticalRL.OnlineRL
