import Formalization.Online.QLearning.RateSquared
import Formalization.Online.QLearning.ActualStackWeightedTail

/-! Source learning-rate proxy for the fixed-row concentration step. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators NNReal

theorem qLearning_rate_proxy_le (H n : ℕ) (hH : 0 < H) (hn : 0 < n) :
    ((∑ i : Fin n, ‖onlineQRateWeight H n (i.val+1)‖₊ ^ 2 *
      (‖(H:ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ) ≤ (H:ℝ)^3/(2*(n:ℝ)) := by
  have hsq := qLearning_rate_fin_squared_le H n hH hn
  have hH0 : (0:ℝ) ≤ H := by positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hfactor : (0:ℝ) ≤ ((H:ℝ)/2)^2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hsq hfactor
  have hid : ((∑ i : Fin n, ‖onlineQRateWeight H n (i.val+1)‖₊ ^ 2 *
      (‖(H:ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ) =
      (∑ i : Fin n, (onlineQRateWeight H n (i.val+1))^2) * ((H:ℝ)/2)^2 := by
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, abs_of_nonneg hH0, Finset.sum_mul, sq_abs]
  rw [hid]
  have heq : (2*(H:ℝ)/(n:ℝ))*((H:ℝ)/2)^2 = (H:ℝ)^3/(2*(n:ℝ)) := by
    field_simp
    <;> ring
  linarith
end StatisticalRL.OnlineRL
