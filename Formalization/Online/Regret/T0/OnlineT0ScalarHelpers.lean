import Formalization.Online.Regret.T0.OnlineT0SourceDefinition

/-! Same-experiment suffix proof component: OnlineT0ScalarHelpers.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineT0Suffix_sqrt_radius_absorb
    (S A H : ℝ) (x L I : ℝ)
    (hSAH : 1 ≤ S * A * H) (hx : 0 ≤ x) (hL : 0 ≤ L)
    (hI : 1024 * L ≤ I) :
    4 * Real.sqrt (x * L) ≤
      (1 / 8 : ℝ) * Real.sqrt (S * A * H * x * I) := by
  have hprod : 1024 * x * L ≤ S * A * H * x * I := by
    have hmul := mul_le_mul_of_nonneg_left hI
      (by positivity : 0 ≤ x * (S * A * H))
    have hbase := mul_le_mul_of_nonneg_right hSAH
      (show 0 ≤ 1024 * x * L by positivity)
    nlinarith
  have hsquare :
      (4 * Real.sqrt (x * L))^2 ≤
        ((1 / 8 : ℝ) * Real.sqrt (S * A * H * x * I))^2 := by
    have hI0 : 0 ≤ I := le_trans (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024) hL) hI
    have hfac : 0 ≤ S * A * H := le_trans (by norm_num) hSAH
    have hleft := Real.sq_sqrt (mul_nonneg hx hL)
    have hright := Real.sq_sqrt (mul_nonneg (mul_nonneg hfac hx) hI0)
    nlinarith
  have hleft : 0 ≤ 4 * Real.sqrt (x * L) := by positivity
  have hright : 0 ≤ (1 / 8 : ℝ) * Real.sqrt (S * A * H * x * I) := by positivity
  nlinarith

theorem onlineT0Suffix_w1w2_scalar
    (w₁ w₂ rV rDsmall rDbig lin₁ lin₂ p₂ : ℝ)
    (hW₁ : w₁ ≤ (1 / 8 : ℝ) * rV + (1 / 8 : ℝ) * rDsmall +
      lin₁)
    (hW₂ : w₂ ≤ (1 / 8 : ℝ) * rDbig + lin₂)
    (hr : rDsmall ≤ rDbig)
    (hp : lin₁ + lin₂ ≤ p₂) :
    w₁ + w₂ ≤ (1 / 8 : ℝ) * rV + (1 / 4 : ℝ) * rDbig +
      p₂ := by
  have hr' := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hsum := add_le_add hW₁ hW₂
  linarith

theorem onlineT0Suffix_log_factor (L : ℝ) (hL : 1 ≤ L) :
    2 * L ≤ 4 * L^2 := by
  have hLsq : L ≤ L^2 := by nlinarith [sq_nonneg (L - 1)]
  calc
    2 * L ≤ 2 * L^2 := by nlinarith [hLsq]
    _ ≤ 4 * L^2 := by nlinarith [sq_nonneg L]

theorem onlineT0Suffix_random_radius_absorb (q L : ℝ) (hq : 0 ≤ q)
    (hLnonneg : 0 ≤ L) (hL : 1 ≤ L) :
    Real.sqrt (2 * q * L) ≤ 2 * Real.sqrt q * L := by
  have hLfactor := onlineT0Suffix_log_factor L hL
  have hmul := mul_le_mul_of_nonneg_left hLfactor hq
  have hsquare : 2 * q * L ≤ (2 * Real.sqrt q * L)^2 := by
    calc
      2 * q * L = q * (2 * L) := by ring
      _ ≤ q * (4 * L^2) := hmul
      _ = 4 * q * L^2 := by ring
      _ = (2 * Real.sqrt q * L)^2 := by
        calc
          4 * q * L^2 = 4 * (Real.sqrt q)^2 * L^2 := by rw [Real.sq_sqrt hq]
          _ = (2 * Real.sqrt q * L)^2 := by ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Real.sqrt_nonneg _)) hLnonneg
  · exact hsquare

theorem onlineT0Suffix_five_plus_two (x L : ℝ) :
    5 * x * L + 2 * x * L = 7 * x * L := by ring

theorem onlineT0Suffix_mass_coefficient (S F : ℝ) (hS : 1 ≤ S)
    (hF : 0 ≤ F) :
    (1 / 8 : ℝ) * S * F + (1 / 8 : ℝ) * S^2 * F ≤
      (1 / 4 : ℝ) * S^2 * F := by
  have hsq : S ≤ S^2 := by
    have hm := mul_le_mul_of_nonneg_right hS (show 0 ≤ S by positivity)
    simpa [pow_two] using hm
  have hmul := mul_le_mul_of_nonneg_right hsq hF
  calc
    (1 / 8 : ℝ) * S * F + (1 / 8 : ℝ) * S^2 * F =
        (1 / 8 : ℝ) * (S * F) + (1 / 8 : ℝ) * (S^2 * F) := by ring
    _ ≤ (1 / 8 : ℝ) * (S^2 * F) + (1 / 8 : ℝ) * (S^2 * F) :=
      add_le_add (mul_le_mul_of_nonneg_left hmul (by norm_num)) le_rfl
    _ = (1 / 4 : ℝ) * S^2 * F := by ring


end StatisticalRL.OnlineRL
