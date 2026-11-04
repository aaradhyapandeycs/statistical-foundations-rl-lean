import Formalization.Online.Regret.MVP.Probability.MVPLogBase

/-! Logarithmic cost of the verified monotone-profile cover. -/
namespace StatisticalRL.OnlineRL

theorem mvp_logProfile_le (P d K : ℝ) (hP : 0 < P) (hd : 1 ≤ d) (hK : 2 ≤ K)
    (hcard : P ≤ (4*d*K) ^ (d*(Real.log K/Real.log 2)+1)) :
    Real.log P ≤ 16*d*(Real.log K/Real.log 2)^2*Real.log (3*d) := by
  let x := Real.log K/Real.log 2
  let z := Real.log (3*d)
  have hx : 1 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2
    simpa using Real.log_le_log (by norm_num : (0:ℝ)<2) hK
  have hz : 0 ≤ z := by
    dsimp [z]
    apply Real.log_nonneg
    nlinarith
  have hdx : 1 ≤ d*x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hx)]
  have hbase : 0 ≤ Real.log (4*d*K) := Real.log_nonneg (by nlinarith)
  have hbound : Real.log (4*d*K) ≤ 8*x*z := mvp_log4dK_le d K hd hK
  have hcoeff : d*x+1 ≤ 2*d*x := by linarith
  have hmul := mul_le_mul hcoeff hbound hbase (by positivity : 0 ≤ 2*d*x)
  have hlog := Real.log_le_log hP hcard
  rw [Real.log_rpow (by positivity : 0 < 4*d*K)] at hlog
  dsimp [x,z] at hmul
  nlinarith
end StatisticalRL.OnlineRL
