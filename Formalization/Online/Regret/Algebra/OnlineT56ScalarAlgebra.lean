import Formalization.Online.Regret.W1.OnlineW1IotaBounds
import Formalization.Online.Regret.Algebra.OnlineVarianceRadiusAlgebra

/-! Same-experiment suffix proof component: OnlineT56ScalarAlgebra.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL

theorem onlineT56_sqrt_product_young (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith only [sq_nonneg (a - b)]

theorem onlineT56_quarter_low_radius (P B V : ℝ)
    (hP : 0 ≤ P) (hB : 0 ≤ B) (hV : V ≤ 2 * B) :
    (1 / 4 : ℝ) * Real.sqrt (P * V) ≤ B + (1 / 4 : ℝ) * P := by
  have hm : P * V ≤ P * (2 * B) := mul_le_mul_of_nonneg_left hV hP
  have hr : Real.sqrt (P * (2 * B)) ≤ 4 * B + P := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [sq_nonneg (P - 4 * B), mul_nonneg hP hB]
  have ht := (Real.sqrt_le_sqrt hm).trans hr
  linarith only [ht]

/-- This is the last scalar step of the printed simplified T5 estimate.
P=SAH³I, Q=S²AH³I, B=KH², V=T6low, D=T6diff. -/
theorem onlineT56_T5_simplify (T P Q B V D Tbonus : ℝ)
    (hT : 0 ≤ T) (hP : 0 ≤ P) (hPQ : P ≤ Q) (hB : 0 ≤ B)
    (hV : V ≤ 2 * B)
    (hbase : T ≤ Tbonus + 2 * B + (1 / 4 : ℝ) * Real.sqrt (P * V) +
      (1 / 4 : ℝ) * Real.sqrt (Q * D) + (1 / 4 : ℝ) * Q)
    (hbonus : Tbonus ≤ Real.sqrt (P * T) + P) :
    T ≤ 6 * B + (1 / 2 : ℝ) * Real.sqrt (Q * D) + 4 * Q := by
  have hlow := onlineT56_quarter_low_radius P B V hP hB hV
  have hy := onlineT56_sqrt_product_young P T hP hT
  linarith only [hbase,hbonus,hlow,hy,hPQ]

theorem onlineT56_low_sqrt_absorb (H K L : ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlarge : 2 * H^2 * L ≤ K) :
    Real.sqrt (2 * H^6 * K * L) ≤ K * H^2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hm := mul_le_mul_of_nonneg_right hlarge
      (mul_nonneg hK (pow_nonneg hH 4))
    nlinarith only [hm]

theorem onlineT56_low_simplify (H K L V : ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlarge : 2 * H^2 * L ≤ K)
    (hbase : V ≤ K * H^2 + Real.sqrt (2 * H^6 * K * L)) :
    V ≤ 2 * K * H^2 := by
  have hr := onlineT56_low_sqrt_absorb H K L hH hK hL hlarge
  linarith only [hbase,hr]

/-- The source iota dominates this stronger numerical coefficient on K≥2. -/
theorem onlineT56_source_iota_large
    (S A H K : ℕ) (δ' : ℝ) (hS : 0 < S) (hA : 0 < A)
    (hH : 0 < H) (hK : 2 ≤ K) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100) :
    20000 * Real.log (1 / δ') ≤ onlineW1SourceIota S A H K δ' := by
  let b := Real.log K / Real.log 2
  let g := Real.log (3 * S * A * H : ℝ)
  let L := Real.log (1 / δ')
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
  have hL : 0 ≤ L := (onlineSmallConfidence_log_ge_one δ' hδ' hδ'small).trans' (by norm_num)
  have hbcube : 1 ≤ b^3 := by nlinarith only [hb, sq_nonneg (b - 1)]
  have hbg : (1 / 2 : ℝ) ≤ b^3 * g := by
    have hm := mul_le_mul_of_nonneg_right hbcube (show 0 ≤ g by linarith only [hg])
    linarith only [hm,hg]
  have hm := mul_le_mul_of_nonneg_right hbg hL
  change 20000 * L ≤ 40000 * b^3 * g * L
  nlinarith only [hm]

theorem onlineT56_noise_radius_absorb (H L C x : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hx : 0 ≤ x)
    (hC : 4096 * H^2 * L ≤ C) :
    8 * H * Real.sqrt (x * L) ≤ (1 / 8 : ℝ) * Real.sqrt (C * x) := by
  have hsq : (64 * H * Real.sqrt (x * L))^2 ≤ C * x := by
    have hm := mul_le_mul_of_nonneg_right hC hx
    have heq : (64 * H * Real.sqrt (x * L))^2 = 4096 * H^2 * L * x := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hx hL)]
      ring
    rw [heq]
    exact hm
  have hr := Real.le_sqrt_of_sq_le hsq
  linarith only [hr]

/-- Source T5 plus W3 and the T8 event, after coefficient absorption. -/
theorem onlineT56_T5_coarse_from_radii (T W3 T8 Tbonus B P Q V D H L : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hP : 4096 * H^2 * L ≤ P) (hPQ : P ≤ Q)
    (hT : T ≤ W3 + T8 + Tbonus + 2 * B)
    (hW : W3 ≤ (1 / 8 : ℝ) * Real.sqrt (P * V) +
      (1 / 8 : ℝ) * Real.sqrt (Q * D) + (1 / 8 : ℝ) * Q)
    (h8 : T8 ≤ 8 * H * Real.sqrt (V * L) +
      8 * H * Real.sqrt (D * L) + 5 * H^2 * L) :
    T ≤ Tbonus + 2 * B + (1 / 4 : ℝ) * Real.sqrt (P * V) +
      (1 / 4 : ℝ) * Real.sqrt (Q * D) + (1 / 4 : ℝ) * Q := by
  have hVrad := onlineT56_noise_radius_absorb H L P V hH hL hV hP
  have hDrad := onlineT56_noise_radius_absorb H L Q D hH hL hD (hP.trans hPQ)
  have hHL : 0 ≤ H^2 * L := mul_nonneg (sq_nonneg H) hL
  have hlinear : 5 * H^2 * L ≤ (1 / 8 : ℝ) * Q := by
    linarith only [hP,hPQ,hHL]
  linarith only [hT,hW,h8,hVrad,hDrad,hlinear]

end StatisticalRL.OnlineRL
