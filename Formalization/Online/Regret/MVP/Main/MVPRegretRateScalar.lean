import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! scalar rate from explicit MVP component bounds. No event or
algorithmic estimate is asserted by this algebra lemma. -/
namespace StatisticalRL.OnlineRL

theorem mvp_main_regret_rate_large (d H K I T2 T5 T6 W4 R : ℝ)
    (hd : 1≤d) (hH : 1≤H) (hI : 1≤I) (hK : d*I≤K)
    (h5n : 0≤T5) (h6n : 0≤T6) (hsum : T5+T6 ≤ 101*K*H^2*I)
    (h2 : T2 ≤ (1/2 : ℝ)*Real.sqrt (d*T5*I)+(1/2 : ℝ)*d*H*I)
    (h4 : W4 ≤ Real.sqrt (d*T6*I)+d*H*I)
    (hR : R ≤ W4+T2+(Real.sqrt (T6*I)+H*I)+Real.sqrt (K*H^2*I)) :
    R ≤ 100*Real.sqrt (d*K*H^2)*I := by
  let P := Real.sqrt (d*K*H^2)*I
  have hd0 : 0≤d := by linarith
  have hH0 : 0≤H := by linarith
  have hI0 : 0≤I := by linarith
  have hK0 : 0≤K := by nlinarith
  have hP : 0≤P := by dsimp [P]; positivity
  have hbase : 0≤d*K*H^2 := by positivity
  have hbaseSq := Real.sq_sqrt hbase
  have hiI : 0≤I^2-I := by nlinarith [sq_nonneg (I-1)]
  have h5upper : T5 ≤ 101*K*H^2*I := by linarith
  have h6upper : T6 ≤ 101*K*H^2*I := by linarith
  have hroot5 : Real.sqrt (d*T5*I) ≤ 11*P := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hm := mul_le_mul_of_nonneg_left h5upper (show 0≤d*I by positivity)
      dsimp [P]
      nlinarith only [hm, hbaseSq, mul_nonneg hiI hbase]
  have hroot6 : Real.sqrt (d*T6*I) ≤ 11*P := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hm := mul_le_mul_of_nonneg_left h6upper (show 0≤d*I by positivity)
      dsimp [P]
      nlinarith only [hm, hbaseSq, mul_nonneg hiI hbase]
  have hsmall : Real.sqrt (T6*I) ≤ Real.sqrt (d*T6*I) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (show 0≤T6*I by positivity)]
  have hdK : d≤K := by nlinarith [mul_nonneg (sub_nonneg.mpr hI) hd0]
  have hmass : d*H*I ≤ P := by
    have hroot : d*H ≤ Real.sqrt (d*K*H^2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_nonneg (sub_nonneg.mpr hdK) (show 0≤d*H^2 by positivity)]
    dsimp [P]
    exact mul_le_mul_of_nonneg_right hroot hI0
  have hunit : H*I ≤ P := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) (show 0≤H*I by positivity)]
  have hlast : Real.sqrt (K*H^2*I) ≤ P := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hP
    · dsimp [P]
      have hdi : 1≤d*I := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) hI0]
      have hm := mul_nonneg (sub_nonneg.mpr hdi) (show 0≤K*H^2*I by positivity)
      have hsqr : (Real.sqrt (d*K*H^2)*I)^2 = d*K*H^2*I^2 := by rw [mul_pow, hbaseSq]
      nlinarith only [hm, hsqr]
  have hfinal : R ≤ 100*P := by
    linarith only [h2,h4,hR,hroot5,hroot6,hsmall,hmass,hunit,hlast,hP]
  dsimp [P] at hfinal
  nlinarith only [hfinal]
end StatisticalRL.OnlineRL
