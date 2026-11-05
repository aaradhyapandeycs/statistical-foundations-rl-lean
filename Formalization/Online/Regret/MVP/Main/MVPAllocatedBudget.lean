import Formalization.Online.Regret.MVP.Main.MVPEventCollector
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Allocation instantiation. Intermediate arithmetic; not the
probability theorem. -/
namespace StatisticalRL.OnlineRL

theorem mvp_main_allocated_failure_budget (S A H K : ℕ) (δ : ℝ)
    (hS : 0<S) (hA : 0<A) (hH : 0<H) (hK : 2≤K) (hδ : 0≤δ) :
    (2*(S : ℝ)*A*H*K + 1 + 4*(Real.log K/Real.log 2) +
      2*Real.log (K*H : ℕ) + 4*(S : ℝ)*A*H*K)*
      onlineSourceOptimismDeltaPrime δ S A H K ≤ δ := by
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast (show 1≤K by omega)
  have hd : (1 : ℝ) ≤ (S : ℝ)*A*H :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs ha) hh
  have hHd : (H : ℝ) ≤ (S : ℝ)*A*H := by
    have hsa : (1 : ℝ) ≤ (S : ℝ)*A := one_le_mul_of_one_le_of_one_le hs ha
    nlinarith [mul_nonneg (sub_nonneg.mpr hsa) (show 0≤(H : ℝ) by positivity)]
  have hlog := mvp_main_log_budget_bounds K H hK hH
  have h := mvp_main_failure_budget_scalar ((S : ℝ)*A*H) K H δ
    (Real.log K/Real.log 2) (Real.log (K*H : ℕ)) hd hk hh hδ hlog.1 hlog.2 hHd
  have heq : onlineSourceOptimismDeltaPrime δ S A H K =
      δ/(100*(((S : ℝ)*A*H)*K)^2) := by
    unfold onlineSourceOptimismDeltaPrime
    congr 1
    ring
  rw [heq]
  simpa only [mul_assoc] using h
end StatisticalRL.OnlineRL
