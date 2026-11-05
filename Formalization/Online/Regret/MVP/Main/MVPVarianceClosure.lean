import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! scalar closure from explicit MVP source component inequalities.
This is a conditional algebra lemma, not an actual-probability certificate. -/
namespace StatisticalRL.OnlineRL

theorem mvp_main_young_small (H K T : ℝ) (hH : 0≤H) (hK : 0≤K) (hT : 0≤T) :
    H*Real.sqrt (K*T) ≤ (1/8 : ℝ)*T + 2*K*H^2 := by
  have hroot : Real.sqrt (K*T) = Real.sqrt K * Real.sqrt T := Real.sqrt_mul hK T
  rw [hroot]
  nlinarith [sq_nonneg (Real.sqrt T - 4*H*Real.sqrt K), Real.sq_sqrt hK, Real.sq_sqrt hT]

theorem mvp_main_young_large (H K T : ℝ) (hH : 0≤H) (hK : 0≤K) (hT : 0≤T) :
    4*H*Real.sqrt (K*T) ≤ (1/4 : ℝ)*T + 16*K*H^2 := by
  have hroot : Real.sqrt (K*T) = Real.sqrt K * Real.sqrt T := Real.sqrt_mul hK T
  rw [hroot]
  nlinarith [sq_nonneg (Real.sqrt T - 8*H*Real.sqrt K), Real.sq_sqrt hK, Real.sq_sqrt hT]

theorem mvp_main_T5_T6_closure (d H K I T2 T5 T6 W3 W4 : ℝ)
    (hd : 1≤d) (hH : 1≤H) (hI : 1≤I) (hK : d*I≤K)
    (h5n : 0≤T5) (h6n : 0≤T6)
    (h2 : T2 ≤ (1/2 : ℝ)*Real.sqrt (d*T5*I) + (1/2 : ℝ)*d*H*I)
    (h4 : W4 ≤ Real.sqrt (d*T6*I) + d*H*I)
    (h3 : W3 ≤ Real.sqrt (d*H^2*T6*I) + d*H^2*I)
    (h5 : T5 ≤ W3 + 2*H*T2 + Real.sqrt (H^2*T6*I) + K*H^2*I)
    (h6 : T6 ≤ 4*H*T2 + 4*H*W4 + K*H^2*I) :
    T5+T6 ≤ 101*K*H^2*I := by
  have hH0 : 0≤H := by linarith
  have hK0 : 0≤K := by nlinarith
  have hI0 : 0≤I := by linarith
  have hd0 : 0≤d := by linarith
  have hdi : 0≤d*I := by positivity
  have hI_le_K : I≤K := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) hI0]
  have hmass : d*H^2*I ≤ K*H^2*I := by
    have hm := mul_le_mul_of_nonneg_right hK (show 0≤H^2 by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hI) (show 0≤K*H^2 by positivity)]
  have hroot5 : Real.sqrt (d*T5*I) ≤ Real.sqrt (K*T5) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) h5n]
  have hroot6 : Real.sqrt (d*T6*I) ≤ Real.sqrt (K*T6) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) h6n]
  have hrootH : Real.sqrt (d*H^2*T6*I) ≤ H*Real.sqrt (K*T6) := by
    have hsq : 0≤K*T6 := by positivity
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hsq, mul_nonneg (sub_nonneg.mpr hK) (show 0≤H^2*T6 by positivity)]
  have hrootI : Real.sqrt (H^2*T6*I) ≤ H*Real.sqrt (K*T6) := by
    have hsq : 0≤K*T6 := by positivity
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hsq, mul_nonneg (sub_nonneg.mpr hI_le_K) (show 0≤H^2*T6 by positivity)]
  have hy5 := mvp_main_young_small H K T5 hH0 hK0 h5n
  have hy6 := mvp_main_young_small H K T6 hH0 hK0 h6n
  have hy64 := mvp_main_young_large H K T6 hH0 hK0 h6n
  have h2H := mul_le_mul_of_nonneg_left h2 (show 0≤2*H by positivity)
  have h4H := mul_le_mul_of_nonneg_left h4 (show 0≤4*H by positivity)
  have hR5 := mul_le_mul_of_nonneg_left hroot5 hH0
  have hR6 := mul_le_mul_of_nonneg_left hroot6 (show 0≤4*H by positivity)
  have hKH : K*H^2 ≤ K*H^2*I := by nlinarith [mul_nonneg (sub_nonneg.mpr hI) (show 0≤K*H^2 by positivity)]
  have hm : 0≤K*H^2*I := by positivity
  nlinarith
end StatisticalRL.OnlineRL
