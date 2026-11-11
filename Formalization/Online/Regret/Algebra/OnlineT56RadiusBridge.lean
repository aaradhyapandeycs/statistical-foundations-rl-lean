import Formalization.Online.Regret.Algebra.OnlineT56ScalarAlgebra

/-! Same-experiment suffix proof component: OnlineT56RadiusBridge.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL

theorem onlineT56_sqrt_square_mul (H z : ℝ) (hH : 0 ≤ H) :
    Real.sqrt (H^2 * z) = H * Real.sqrt z := by
  rw [Real.sqrt_mul (sq_nonneg H), Real.sqrt_sq hH]

theorem onlineT56_T8_radius_expand (H U V D L : ℝ)
    (hH : 0 ≤ H) (hU : 0 ≤ U) (hV : 0 ≤ V) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hcompare : U ≤ 2 * V + 2 * D) :
    Real.sqrt (32 * H^2 * U * L) + 5 * H^2 * L ≤
      8 * H * Real.sqrt (V * L) + 8 * H * Real.sqrt (D * L) + 5 * H^2 * L := by
  have heq : 32 * H^2 * U * L = (2 * H)^2 * (8 * U * L) := by ring
  rw [heq, onlineT56_sqrt_square_mul (2 * H) _ (by positivity)]
  have hr := onlineVarianceRadius_le_policy_difference U V D L hU hV hD hL hcompare
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * H by positivity)
  nlinarith only [hm]

theorem onlineT56_scaled_T2_bound (H J T T2 : ℝ) (hH : 0 ≤ H)
    (hbonus : T2 ≤ (1 / 2 : ℝ) * Real.sqrt (J * T) + (1 / 2 : ℝ) * H * J) :
    2 * H * T2 ≤ Real.sqrt ((H^2 * J) * T) + H^2 * J := by
  have heq : (H^2 * J) * T = H^2 * (J * T) := by ring
  rw [heq, onlineT56_sqrt_square_mul H _ hH]
  have hm := mul_le_mul_of_nonneg_left hbonus (show 0 ≤ 2 * H by positivity)
  nlinarith only [hm]

theorem onlineT56_source_coefficient_dominates_noise (J H I L : ℝ)
    (hJ : 1 ≤ J) (hL : 0 ≤ L) (hI : 4096 * L ≤ I) :
    4096 * H^2 * L ≤ J * H^2 * I := by
  have hI0 : 0 ≤ I := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) hL).trans hI
  have hJI : I ≤ J * I := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ hI0
  have hm := mul_le_mul_of_nonneg_left (hI.trans hJI) (sq_nonneg H)
  nlinarith only [hm]

theorem onlineT56_largeK_implies_logCap (J H I K L : ℝ)
    (hJ : 1 ≤ J) (hL : 0 ≤ L) (hI : 2 * L ≤ I)
    (hK : J * H^2 * I ≤ K) :
    2 * H^2 * L ≤ K := by
  have hI0 : 0 ≤ I := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL).trans hI
  have hJI : I ≤ J * I := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ hI0
  have hm := mul_le_mul_of_nonneg_left (hI.trans hJI) (sq_nonneg H)
  have heq : H^2 * (J * I) = J * H^2 * I := by ring
  calc
    2 * H^2 * L = H^2 * (2 * L) := by ring
    _ ≤ H^2 * (J * I) := hm
    _ = J * H^2 * I := heq
    _ ≤ K := hK

end StatisticalRL.OnlineRL
