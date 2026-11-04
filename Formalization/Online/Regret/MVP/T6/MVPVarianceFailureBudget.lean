import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Peeling failure allocation; independent of the trajectory. -/
namespace StatisticalRL.OnlineRL

theorem mvp_t6_failure_budget (S A H K : ℕ) (δ : ℝ)
    (hS : 0<S) (hA : 0<A) (hδ : 0≤δ) :
    2*(Nat.log2 (K*H) : ℝ)*δ ≤ 4*(S : ℝ)*A*H*K*δ := by
  have hj : Nat.log2 (K*H) ≤ K*H := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 _
  have hjr : (Nat.log2 (K*H) : ℝ) ≤ (K : ℝ)*H := by exact_mod_cast hj
  have hs : (1:ℝ) ≤ S := by exact_mod_cast hS
  have ha : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hsa : (1:ℝ) ≤ (S : ℝ)*A := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ha)]
  have hkh : 0 ≤ (K:ℝ)*H := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hsa) hkh
  have hc : 2*(Nat.log2 (K*H) : ℝ) ≤ 4*(S : ℝ)*A*H*K := by nlinarith
  exact mul_le_mul_of_nonneg_right hc hδ
end StatisticalRL.OnlineRL
