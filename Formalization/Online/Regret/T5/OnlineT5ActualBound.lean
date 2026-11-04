import Formalization.Online.Regret.T5.OnlineT5ActualShift

/-! Actual-law variance and gap proof component: OnlineT5ActualBound.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineActualT5_le_W3_T8_T2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    onlineActualT5 H K hH E initial fallback path δ c₁ c₂ ≤
      (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) +
      onlineActualT8 H K hH E initial fallback path δ c₁ c₂ +
      2 * (H : ℝ) * onlineActualT2 H K hH E initial fallback path δ c₁ c₂ +
      2 * (K : ℝ) * (H : ℝ)^2 := by
  classical
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    onlineT5_actual_episode_remainder_bound H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ k)
  have hrem : onlineT5ActualSquareRemainder H K hH E initial fallback path δ c₁ c₂ ≤
      2 * (H : ℝ) * onlineActualT2 H K hH E initial fallback path δ c₁ c₂ +
      2 * (K : ℝ) * (H : ℝ)^2 := by
    rw [onlineActualT2_eq_sum_points H K hH E initial fallback path δ c₁ c₂]
    unfold onlineT5ActualSquareRemainder
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ k : Fin K, 2 * (H : ℝ) * ((∑ h : Fin H, onlineActualT2Point H K hH E initial fallback path δ c₁ c₂ h k) + H) := hsum
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  rw [onlineActualT5_eq_W3_add_T8_add_remainder H K hH E initial fallback path δ c₁ c₂]
  linarith
end StatisticalRL.OnlineRL
