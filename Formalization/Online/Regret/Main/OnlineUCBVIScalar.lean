import Formalization.Online.Regret.W1.OnlineW1IotaBounds
import Formalization.Probability.OnlineT56ScalarAlgebra

/-! Scalar intermediates for the corrected K≥2 UCBVI route. All estimates
are explicit premises; no actual-path or confidence result is asserted. -/
namespace StatisticalRL.OnlineRL

/-- The penultimate T2 mass term is sharper than its printed weakening. -/
theorem onlineUCBVI_mass_coeff (S F : ℝ) (hS : 1 ≤ S) (hF : 0 ≤ F) :
    ((1 / 4 : ℝ) * S^2 + (3 / 2 : ℝ) * S) * F ≤
      (7 / 4 : ℝ) * S^2 * F := by
  have hSsq : S ≤ S^2 := by nlinarith [sq_nonneg (S - 1)]
  have hm := mul_le_mul_of_nonneg_right hSsq hF
  nlinarith only [hm]

/-- Explicit Young step, with the source's horizon scaling. -/
theorem onlineUCBVI_sqrt_gap_young (H C D : ℝ) (hH : 0 < H)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt (C * D) ≤ D / (4 * H^2) + H^2 * C := by
  have ha : 0 ≤ D / (2 * H^2) := by positivity
  have hb : 0 ≤ 2 * H^2 * C := by positivity
  have hy := onlineT56_sqrt_product_young (D / (2 * H^2)) (2 * H^2 * C) ha hb
  have heq : (D / (2 * H^2)) * (2 * H^2 * C) = C * D := by
    field_simp
  rw [heq] at hy
  convert hy using 1 <;> ring

/-- The nested square-root term appearing after substitution into T2.
The parameters a, q, d are nonnegative and S is a positive state count. -/
theorem onlineUCBVI_nested_root (a q d S : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hd : 0 ≤ d) (hS : 0 < S) :
    Real.sqrt (a * Real.sqrt (q * d) / 8) ≤
      (1 / 8 : ℝ) * Real.sqrt (a * d / S) +
      (1 / 2 : ℝ) * Real.sqrt (a * q * S) := by
  have hrootprod : Real.sqrt (a * d / S) * Real.sqrt (a * q * S) =
      a * Real.sqrt (q * d) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ a * d / S)]
    have heq : (a * d / S) * (a * q * S) = a^2 * (q * d) := by
      field_simp
    rw [heq, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  have hu := Real.sqrt_nonneg (a * d / S)
  have hv := Real.sqrt_nonneg (a * q * S)
  have hqdr := Real.sqrt_nonneg (q * d)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith only [hrootprod, mul_nonneg hu hv, sq_nonneg ((1 / 8 : ℝ) * Real.sqrt (a * d / S) -
        (1 / 2 : ℝ) * Real.sqrt (a * q * S))]

/-- Subadditivity of three nonnegative square-root terms. -/
theorem onlineUCBVI_sqrt_three (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have hx' := Real.sq_sqrt hx
  have hy' := Real.sq_sqrt hy
  have hz' := Real.sq_sqrt hz
  have hxy := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  have hxz := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg z)
  have hyz := mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith only [hx', hy', hz', hxy, hxz, hyz]

/-- Substitute the simplified T5 estimate into the T2 square-root charge.
The final linear charge z remains explicit for the sharper mass accounting. -/
theorem onlineUCBVI_T2_from_T5 (a b q d S T5 T2 z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hd : 0 ≤ d) (hS : 0 < S)
    (hT5 : T5 ≤ 6 * b + (1 / 2 : ℝ) * Real.sqrt (q * d) + 4 * q)
    (hT2 : T2 ≤ (1 / 2 : ℝ) * Real.sqrt (a * T5) + z) :
    T2 ≤ (1 / 2 : ℝ) * Real.sqrt (6 * a * b) +
      (1 / 8 : ℝ) * Real.sqrt (a * d / S) +
      (1 / 2 : ℝ) * Real.sqrt (a * q * S) + Real.sqrt (a * q) + z := by
  have hmul := mul_le_mul_of_nonneg_left hT5 ha
  have hr := Real.sqrt_le_sqrt hmul
  have hsplit := onlineUCBVI_sqrt_three (6 * a * b) (a * Real.sqrt (q * d) / 2) (4 * a * q)
    (by positivity) (by positivity) (by positivity)
  have hsum : a * (6 * b + (1 / 2 : ℝ) * Real.sqrt (q * d) + 4 * q) =
      6 * a * b + a * Real.sqrt (q * d) / 2 + 4 * a * q := by ring
  rw [hsum] at hr
  have hmid : (1 / 2 : ℝ) * Real.sqrt (a * Real.sqrt (q * d) / 2) =
      Real.sqrt (a * Real.sqrt (q * d) / 8) := by
    have heq : a * Real.sqrt (q * d) / 8 = (1 / 4 : ℝ) * (a * Real.sqrt (q * d) / 2) := by ring
    rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
  have hlast : Real.sqrt (4 * a * q) = 2 * Real.sqrt (a * q) := by
    have heq : 4 * a * q = 4 * (a * q) := by ring
    rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hnested := onlineUCBVI_nested_root a q d S ha hq hd hS
  rw [hlast] at hsplit
  linarith only [hT2, hr, hsplit, hmid, hnested]

/-- Final self-bounding arithmetic with all component estimates visible.
`R` is the nonnegative leading source square-root expression and `B` is the
nonnegative additive source coefficient. -/
theorem onlineUCBVI_T0_self_bound (H R B L T0 D : ℝ)
    (hH : 1 ≤ H) (hR : 0 ≤ R) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hD : 0 ≤ D) (hLbudget : H^2 * L ≤ B)
    (hT0 : T0 ≤ 10 * R + Real.sqrt ((B / H^2) * D) + 2 * (B / H))
    (hDbd : D ≤ 2 * H^2 * T0 + 18 * H^2 * L) :
    T0 ≤ 20 * R + 15 * B := by
  have hH0 : 0 < H := by linarith
  have hC : 0 ≤ B / H^2 := by positivity
  have hy := onlineUCBVI_sqrt_gap_young H (B / H^2) D hH0 hC hD
  have hHsq : 0 < H^2 := by positivity
  have hcancel : H^2 * (B / H^2) = B := by field_simp
  have hDdiv : D / (4 * H^2) ≤ (1 / 2 : ℝ) * T0 + (9 / 2 : ℝ) * L := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * H^2)).2
    nlinarith only [hDbd]
  have hdiv : B / H ≤ B := by
    apply (div_le_iff₀ hH0).2
    nlinarith only [hH, hB]
  have hLle : L ≤ B := by
    have hs : 1 ≤ H^2 := by nlinarith [sq_nonneg (H - 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hL]
  rw [hcancel] at hy
  linarith only [hT0, hy, hDdiv, hdiv, hLle]
end StatisticalRL.OnlineRL
