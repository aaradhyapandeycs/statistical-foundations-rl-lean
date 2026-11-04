import Formalization.Online.Regret.T2.OnlineT2ActualCoarse
import Formalization.Online.Regret.T2.OnlineT2SourceAlgebra
import Formalization.Online.Regret.W1.OnlineW1LogBounds

/-! Deterministic corrected-zero-count T₂ bound on the actual path, with the
source iota side condition. This does not assert T₃/T₄ or a regret rate. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineActualT2_le_sourceBound
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ I : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hI : 8 * max (c₁^2) c₂ * (Real.log K / Real.log 2) * Real.log (1 / δ) ≤ I) :
    onlineActualT2 H K hH E initial fallback path δ c₁ c₂ ≤
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H *
        onlineActualT5 H K hH E initial fallback path δ c₁ c₂ * I) +
      (1 / 2 : ℝ) * (Fintype.card State : ℝ) * Fintype.card Action * H^2 * I := by
  let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
  let B := Real.log K / Real.log 2
  let L := Real.log (1 / δ)
  let T := onlineActualT5 H K hH E initial fallback path δ c₁ c₂
  have hB : 1 ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ K by exact_mod_cast hK)
  have hL : 1 ≤ L := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hc₁0 : 0 ≤ c₁ := by linarith
  have hc₂0 : 0 ≤ c₂ := by nlinarith [sq_nonneg c₁]
  have hBL : 1 ≤ B * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hL)]
  have hnon : 0 ≤ 8 * B * L := by positivity
  have hi1 : 8 * c₁^2 * B * L ≤ I := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (c₁^2) c₂) hnon
    nlinarith
  have hi2 : 8 * c₂ * B * L ≤ I := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right (c₁^2) c₂) hnon
    nlinarith
  have hi4 : 4 ≤ I := by
    have hh := mul_le_mul_of_nonneg_left hBL (show 0 ≤ 8 * c₁^2 by positivity)
    nlinarith [sq_nonneg (c₁ - 4)]
  have hT : 0 ≤ T := by
    unfold T onlineActualT5
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hcoarse := onlineActualT2_le_coarseBudget H K hH hK E initial fallback path δ c₁ c₂ (by linarith : 0 ≤ L) hc₁0 hc₂0
  have ha := onlineT2_coarse_to_source A H B L I c₁ c₂ T (by positivity) (by positivity)
    (by linarith) (by linarith) hc₁0 hc₂0 hT hi1 hi2 hi4
  convert hcoarse.trans ha using 1 <;> dsimp [A, T] <;> ring_nf
end StatisticalRL.OnlineRL
