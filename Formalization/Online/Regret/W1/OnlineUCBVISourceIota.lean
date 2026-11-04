import Formalization.Online.Regret.W1.OnlineW1IotaBounds

/-! The exact source iota satisfies the T2 side condition at c₁=4,c₂=16
when K≥2. This is a scalar bound, not an actual-path regret result. -/
namespace StatisticalRL.OnlineRL

theorem onlineUCBVI_iota_ge_20000_log2_mul_log
    (S A H K : ℕ) (δ : ℝ) (hS : 0 < S) (hA : 0 < A)
    (hH : 0 < H) (hK : 2 ≤ K) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) :
    20000 * (Real.log K / Real.log 2) * Real.log (1 / δ) ≤
      onlineW1SourceIota S A H K δ := by
  let b := Real.log K / Real.log 2
  let g := Real.log (3 * S * A * H : ℝ)
  let L := Real.log (1 / δ)
  have hb : 1 ≤ b := by
    dsimp [b]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ K by exact_mod_cast hK)
  have hg : (1 / 2 : ℝ) ≤ g := by
    have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hbase : (2 : ℝ) ≤ 3 * S * A * H := by
      calc
        (2 : ℝ) ≤ 3 * 1 * 1 * 1 := by norm_num
        _ ≤ 3 * S * A * H := by gcongr
    have hlogbase := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmon := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hbase
    dsimp [g]
    norm_num at hlogbase
    linarith
  have hL : 0 ≤ L := (onlineSmallConfidence_log_ge_one δ hδ hδsmall).trans' (by norm_num)
  have hb3 : b ≤ b^3 := by nlinarith only [hb, sq_nonneg (b - 1), mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg b)]
  have hmul1 := mul_le_mul_of_nonneg_right hb3 (show 0 ≤ g by linarith)
  have hmul2 := mul_le_mul_of_nonneg_left hg (show 0 ≤ b by linarith)
  have hbg : b / 2 ≤ b^3 * g := by nlinarith only [hmul1, hmul2]
  have hm := mul_le_mul_of_nonneg_right hbg hL
  change 20000 * b * L ≤ 40000 * b^3 * g * L
  nlinarith only [hm]

theorem onlineUCBVI_iota_meets_T2_constants
    (S A H K : ℕ) (δ : ℝ) (hS : 0 < S) (hA : 0 < A)
    (hH : 0 < H) (hK : 2 ≤ K) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) :
    8 * max ((4 : ℝ)^2) 16 * (Real.log K / Real.log 2) * Real.log (1 / δ) ≤
      onlineW1SourceIota S A H K δ := by
  have hi := onlineUCBVI_iota_ge_20000_log2_mul_log S A H K δ hS hA hH hK hδ hδsmall
  have hb : 0 ≤ Real.log K / Real.log 2 := by
    positivity
  have hL : 0 ≤ Real.log (1 / δ) := (onlineSmallConfidence_log_ge_one δ hδ hδsmall).trans' (by norm_num)
  norm_num only [show (4 : ℝ)^2 = 16 by norm_num, max_self]
  nlinarith only [hi, mul_nonneg hb hL]
end StatisticalRL.OnlineRL
