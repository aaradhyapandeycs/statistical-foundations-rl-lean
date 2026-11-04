import Formalization.Online.Regret.W1.OnlineUCBVISourceIota
import Formalization.Online.SourceOptimism.GreedySequentialBellmanOptimism
import Mathlib.Tactic

/-! Source iota absorbs the conservative +5 H²L T8 radius for K≥2. -/
namespace StatisticalRL.OnlineRL

theorem mvp_t6_iota_budget (S A H K : ℕ) (δ : ℝ)
    (hS : 0<S) (hA : 0<A) (hH : 0<H) (hK : 2≤K)
    (hδ : 0<δ) (hδsmall : δ≤1/100) :
    4*(K : ℝ)+42*Real.log (1/δ) ≤
      (K : ℝ)*onlineW1SourceIota S A H K δ := by
  let L := Real.log (1/δ)
  let b := Real.log K / Real.log 2
  let I := onlineW1SourceIota S A H K δ
  have hL : 1 ≤ L := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hb : 1 ≤ b := by
    dsimp [b]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2
    simpa using Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤K by exact_mod_cast hK)
  have hi : 20000*b*L ≤ I := onlineUCBVI_iota_ge_20000_log2_mul_log S A H K δ hS hA hH hK hδ hδsmall
  have hi' : 20000*L ≤ I := by
    have hp := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ L by linarith)
    nlinarith
  have hI : 4+42*L ≤ I := by linarith
  have hKR : (1:ℝ) ≤ K := by exact_mod_cast (show 1≤K by omega)
  have hmul := mul_nonneg (show 0≤(K : ℝ) by positivity) (sub_nonneg.mpr hI)
  have hmore := mul_nonneg (sub_nonneg.mpr hKR) (show 0≤L by linarith)
  dsimp [I,L] at *
  nlinarith
end StatisticalRL.OnlineRL
