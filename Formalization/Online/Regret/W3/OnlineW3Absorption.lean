import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar absorption of the actual coarse W₃ budget into the printed iota. -/
namespace StatisticalRL.OnlineRL

theorem onlineW3_coarse_to_iota_algebra
    (S A H L₀ L Q I p d : ℝ)
    (hS : 1 ≤ S) (hA : 0 ≤ A) (hH : 0 ≤ H) (hL₀ : 0 ≤ L₀) (hL : 0 ≤ L)
    (hLle : L₀ ≤ L) (hQ : 0 ≤ Q) (hp : 0 ≤ p) (hd : 0 ≤ d)
    (hi : 4096 * L * Q ≤ I) (hi192 : 192 ≤ I) :
    6 * H^2 * A + Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt (A * Q) +
      Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt (A * Q) +
      (2 * H^2 * L₀ / 3 + S * H^2 * L) * (A * Q) ≤
    (1 / 8 : ℝ) * Real.sqrt (A * H^2 * p * I) +
    (1 / 8 : ℝ) * Real.sqrt (S * A * H^2 * d * I) +
    (1 / 8 : ℝ) * S * A * H^2 * I := by
  have hS0 : 0 ≤ S := by linarith
  have hI : 0 ≤ I := by linarith
  have hX : 0 ≤ A * Q := by positivity
  have hpI : 0 ≤ A * H^2 * p * I := by positivity
  have hdI : 0 ≤ S * A * H^2 * d * I := by positivity
  have hF : 0 ≤ 2 * L₀ * (4 * H^2 * (2 * p + 2 * d)) := by positivity
  have hD : 0 ≤ 2 * (S * L) * (4 * H^2 * d) := by positivity
  have hcross := mul_nonneg (Real.sqrt_nonneg (A * H^2 * p * I))
    (Real.sqrt_nonneg (S * A * H^2 * d * I))
  have hcoefp := mul_le_mul_of_nonneg_right hi (show 0 ≤ A * H^2 * p by positivity)
  have hcoefd := mul_le_mul_of_nonneg_right hi (show 0 ≤ A * H^2 * d by positivity)
  have hLrelp : 0 ≤ (L - L₀) * (Q * A * H^2 * p) := mul_nonneg (sub_nonneg.mpr hLle) (by positivity)
  have hLreld : 0 ≤ (L - L₀) * (Q * A * H^2 * d) := mul_nonneg (sub_nonneg.mpr hLle) (by positivity)
  have hSreld : 0 ≤ (S - 1) * (A * H^2 * d * I) := mul_nonneg (sub_nonneg.mpr hS) (by positivity)
  have hrootf : Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt (A * Q) ≤
      (1 / 8 : ℝ) * Real.sqrt (A * H^2 * p * I) +
        (1 / 16 : ℝ) * Real.sqrt (S * A * H^2 * d * I) := by
    have hl : 0 ≤ Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt (A * Q) := by positivity
    have hr : 0 ≤ (1 / 8 : ℝ) * Real.sqrt (A * H^2 * p * I) +
        (1 / 16 : ℝ) * Real.sqrt (S * A * H^2 * d * I) := by positivity
    have hsq : (Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt (A * Q))^2 ≤
      ((1 / 8 : ℝ) * Real.sqrt (A * H^2 * p * I) +
        (1 / 16 : ℝ) * Real.sqrt (S * A * H^2 * d * I))^2 := by
      nlinarith only [Real.sq_sqrt hF, Real.sq_sqrt hX, Real.sq_sqrt hpI, Real.sq_sqrt hdI,
        hcross, hcoefp, hcoefd, hLrelp, hLreld, hSreld]
    nlinarith only [hsq, hl, hr]
  have hrootd : Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt (A * Q) ≤
      (1 / 16 : ℝ) * Real.sqrt (S * A * H^2 * d * I) := by
    have hl : 0 ≤ Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt (A * Q) := by positivity
    have hr : 0 ≤ (1 / 16 : ℝ) * Real.sqrt (S * A * H^2 * d * I) := by positivity
    have hc := mul_le_mul_of_nonneg_right hi (show 0 ≤ S * A * H^2 * d by positivity)
    have hsq : (Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt (A * Q))^2 ≤
        ((1 / 16 : ℝ) * Real.sqrt (S * A * H^2 * d * I))^2 := by
      nlinarith only [Real.sq_sqrt hD, Real.sq_sqrt hX, Real.sq_sqrt hdI, hc]
    nlinarith only [hsq, hl, hr]
  have hlow := mul_le_mul_of_nonneg_left hi192 (show 0 ≤ A * H^2 by positivity)
  have hlin := mul_le_mul_of_nonneg_left hi (show 0 ≤ S * A * H^2 by positivity)
  have hSA : A * H^2 ≤ S * A * H^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (show 0 ≤ A * H^2 by positivity)]
  have hLrel : 0 ≤ (L - L₀) * (A * H^2 * Q) := mul_nonneg (sub_nonneg.mpr hLle) (by positivity)
  have hSrel : 0 ≤ (S - 1) * (A * H^2 * L * Q) := mul_nonneg (sub_nonneg.mpr hS) (by positivity)
  have hSAI := mul_le_mul_of_nonneg_right hSA hI
  have hSL : 0 ≤ S * A * H^2 * L * Q := by positivity
  nlinarith only [hrootf, hrootd, hlow, hlin, hSAI, hLrel, hSrel, hSL]
end StatisticalRL.OnlineRL
