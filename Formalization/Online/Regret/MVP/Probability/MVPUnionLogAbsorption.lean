import Formalization.Online.Regret.MVP.Probability.MVPUnionLogBound
import Formalization.Online.OnlineZeroCountOptimisticUpdate

/-! Actual profile/choice/level/mask log absorbed by the corrected allocation. -/
namespace StatisticalRL.OnlineRL

theorem mvp_unionLog_absorbed (P J p δ : ℝ) (d K : ℕ)
    (hP : 0 < P) (hJ : 0 < J) (hp : 0 < p) (hδ : 0 < δ) (hδsmall : δ ≤ 1/100)
    (hd : 1 ≤ d) (hK : 2 ≤ K) (hJle : J ≤ K) (hple : p ≤ d*K)
    (hcard : P ≤ (4*(d:ℝ)*K) ^ ((d:ℝ)*(Real.log K/Real.log 2)+1)) :
    32 * Real.log (2*p*(P*((K:ℝ)+1)^d*J*2^d)/δ) * (Real.log K/Real.log 2) ≤
      (d:ℝ) * (40000*(Real.log K/Real.log 2)^3*Real.log (3*d)*Real.log (1/δ)) := by
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
  exact mvp_logBudget_absorbed40 d (Real.log K/Real.log 2) (Real.log (3*d)) (Real.log (1/δ))
    (Real.log (2*p*(P*((K:ℝ)+1)^d*J*2^d)/δ)) hd1 hx hz
    (onlineSmallConfidence_log_ge_one δ hδ hδsmall)
    (mvp_unionLog_le_40B P J p δ d K hP hJ hp hδ hd hK hJle hple hcard)
end StatisticalRL.OnlineRL
