import Formalization.Online.Regret.MVP.Probability.MVPUnionLogBound
import Formalization.Online.OnlineZeroCountOptimisticUpdate

/-! proof: quarter failure budgets and stronger source radius.
No source completion or qualification evidence is supplied by this file alone.
-/
namespace StatisticalRL.OnlineRL

theorem mvp_log_quarter_le_four (δ : ℝ) (hδ : 0 < δ)
    (hq : 1 ≤ Real.log (1/δ)) :
    Real.log (1/(δ/4)) ≤ 4*Real.log (1/δ) := by
  have heq : 1/(δ/4) = 4*(1/δ) := by field_simp [ne_of_gt hδ]
  rw [heq, Real.log_mul (by norm_num) (ne_of_gt (one_div_pos.mpr hδ))]
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  norm_num at h4
  linarith

theorem mvp_splitLogBudget_absorbed (d x z q L : ℝ)
    (hd : 1 ≤ d) (hx : 1 ≤ x) (hz : 1/2 ≤ z) (hq : 1 ≤ q)
    (hL : L ≤ 40*d*x^2*z + 4*q) :
    128*L*x ≤ d*(40000*x^3*z*q) := by
  have hx2 : 1 ≤ x^2 := by nlinarith
  have hdx : 1 ≤ d*x^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hx2)]
  have hB : (1/2:ℝ) ≤ d*x^2*z := by
    have hm := mul_le_mul_of_nonneg_right hdx (show 0 ≤ z by linarith)
    nlinarith
  have hBq : d*x^2*z ≤ d*x^2*z*q := by
    have hm := mul_nonneg (show 0 ≤ d*x^2*z by positivity) (sub_nonneg.mpr hq)
    nlinarith
  have hqB : q ≤ 2*d*x^2*z*q := by
    have hm := mul_le_mul_of_nonneg_right hB (show 0 ≤ q by linarith)
    nlinarith
  have hL' : L ≤ 48*d*x^2*z*q := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hL' (show 0 ≤ 128*x by linarith)
  have hC : 0 ≤ d*x^3*z*q := by positivity
  nlinarith

theorem mvp_unionLog_quarter_absorbed (P J p δ : ℝ) (d K : ℕ)
    (hP : 0 < P) (hJ : 0 < J) (hp : 0 < p) (hδ : 0 < δ)
    (hδsmall : δ ≤ 1/100)
    (hd : 1 ≤ d) (hK : 2 ≤ K) (hJle : J ≤ K) (hple : p ≤ d*K)
    (hcard : P ≤ (4*(d:ℝ)*K) ^ ((d:ℝ)*(Real.log K/Real.log 2)+1)) :
    128*Real.log (2*p*(P*((K:ℝ)+1)^d*J*2^d)/(δ/4))*(Real.log K/Real.log 2) ≤
      (d:ℝ)*(40000*(Real.log K/Real.log 2)^3*Real.log (3*d)*Real.log (1/δ)) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hK2 : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hx : 1 ≤ Real.log K/Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2
    simpa using Real.log_le_log (by norm_num : (0:ℝ)<2) hK2
  have hz : (1/2:ℝ) ≤ Real.log (3*d) := by
    have hbase : (2:ℝ) ≤ 3*(d:ℝ) := by nlinarith
    have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hbase
    norm_num at h1
    linarith
  have hq : 1 ≤ Real.log (1/δ) := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hraw := mvp_unionLog_le_40B P J p (δ/4) d K hP hJ hp
    (by positivity) hd hK hJle hple hcard
  have hsplit := mvp_log_quarter_le_four δ hδ hq
  exact mvp_splitLogBudget_absorbed d (Real.log K/Real.log 2) (Real.log (3*d))
    (Real.log (1/δ))
    (Real.log (2*p*(P*((K:ℝ)+1)^d*J*2^d)/(δ/4))) hd1 hx hz hq
    (by linarith only [hraw, hsplit])

end StatisticalRL.OnlineRL
