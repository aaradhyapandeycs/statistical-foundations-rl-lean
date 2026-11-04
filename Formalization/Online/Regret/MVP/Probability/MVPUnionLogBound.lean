import Formalization.Online.Regret.MVP.Probability.MVPLogProfile
import Formalization.Online.Regret.MVP.Probability.MVPLogUnionDecomposition
import Formalization.Online.Regret.MVP.Probability.MVPLogBudgetScalar

/-! Explicit finite-union logarithm fits the corrected source iota. -/
namespace StatisticalRL.OnlineRL

theorem mvp_unionLog_le_40B (P J p δ : ℝ) (d K : ℕ)
    (hP : 0 < P) (hJ : 0 < J) (hp : 0 < p) (hδ : 0 < δ)
    (hd : 1 ≤ d) (hK : 2 ≤ K) (hJle : J ≤ K) (hple : p ≤ d*K)
    (hcard : P ≤ (4*(d:ℝ)*K) ^ ((d:ℝ)*(Real.log K/Real.log 2)+1)) :
    Real.log (2*p*(P*((K:ℝ)+1)^d*J*2^d)/δ) ≤
      40*(d:ℝ)*(Real.log K/Real.log 2)^2*Real.log (3*d) + Real.log (1/δ) := by
  let x := Real.log K/Real.log 2
  let z := Real.log (3*(d:ℝ))
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hK2 : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0:ℝ) < K := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hx : 1 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ hl2).2
    simpa using Real.log_le_log (by norm_num : (0:ℝ)<2) hK2
  have hz : (1/2:ℝ) ≤ z := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h2 : (2:ℝ) ≤ 3*(d:ℝ) := by nlinarith
    have h3 := Real.log_le_log (by norm_num : (0:ℝ)<2) h2
    dsimp [z]
    norm_num at h
    linarith
  have hz0 : 0 ≤ z := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hd0 : 0 ≤ (d:ℝ) := by linarith
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hlogK : Real.log K ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ hl2).2
    nlinarith only [hlogK0, hl2le]
  have hKpoly : (K:ℝ)+1 ≤ (K:ℝ)^2 := by nlinarith only [hK2]
  have hKplus := Real.log_le_log (show (0:ℝ)<(K:ℝ)+1 by linarith) hKpoly
  rw [Real.log_pow] at hKplus
  norm_num at hKplus
  have hchoice : (d:ℝ)*Real.log ((K:ℝ)+1) ≤ 8*(d:ℝ)*x^2*z := by
    have h1 : Real.log ((K:ℝ)+1) ≤ 2*x := by nlinarith only [hKplus, hlogK]
    have h2 : x ≤ 2*x^2*z := by nlinarith only [hx, hz, sq_nonneg (x-1)]
    have hB : 0 ≤ (d:ℝ)*x^2*z := by positivity
    nlinarith only [mul_nonneg hd0 (sub_nonneg.mpr h1), mul_nonneg hd0 (sub_nonneg.mpr h2), hB]
  have hlevel : Real.log J ≤ 2*(d:ℝ)*x^2*z := by
    have hJlog := Real.log_le_log hJ hJle
    have hx2 : x ≤ x^2 := by nlinarith only [hx]
    have hdx2 : x^2 ≤ (d:ℝ)*x^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg x)]
    have hz2 : (d:ℝ)*x^2 ≤ 2*(d:ℝ)*x^2*z := by nlinarith only [mul_nonneg (show 0 ≤ (d:ℝ)*x^2 by positivity) (show 0 ≤ 2*z-1 by linarith)]
    have h2 : x ≤ 2*(d:ℝ)*x^2*z := hx2.trans (hdx2.trans hz2)
    linarith
  have hmask : (d:ℝ)*Real.log 2 ≤ 2*(d:ℝ)*x^2*z := by
    have h2 : 1 ≤ 2*x^2*z := by nlinarith only [hx, hz, sq_nonneg (x-1)]
    have ha := mul_le_mul_of_nonneg_left hl2le hd0
    have hb := mul_le_mul_of_nonneg_left h2 hd0
    nlinarith only [ha, hb]
  have hpeel : Real.log (2*p) ≤ 8*(d:ℝ)*x^2*z := by
    have hpbase : 2*p ≤ 4*(d:ℝ)*K := by nlinarith only [hple, mul_nonneg hd0 (le_of_lt hKpos)]
    have hlog := Real.log_le_log (show (0:ℝ)<2*p by positivity) hpbase
    have hbase := mvp_log4dK_le d K hd1 hK2
    have hscale : 8*x*z ≤ 8*(d:ℝ)*x^2*z := by
      have hdx : 1 ≤ (d:ℝ)*x := by nlinarith only [hd1, hx, mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hx)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hdx) (show 0 ≤ x*z by positivity)]
    exact hlog.trans (hbase.trans hscale)
  have hprofile := mvp_logProfile_le P d K hP hd1 hK2 hcard
  have hdecomp := mvp_unionLog_decompose P J p δ K d hP hJ hp hδ hKpos
  dsimp [x,z] at hchoice hlevel hmask hpeel
  have hB : 0 ≤ (d:ℝ)*(Real.log K/Real.log 2)^2*Real.log (3*d) := by positivity
  nlinarith only [hdecomp, hprofile, hchoice, hlevel, hmask, hpeel, hB]
end StatisticalRL.OnlineRL
