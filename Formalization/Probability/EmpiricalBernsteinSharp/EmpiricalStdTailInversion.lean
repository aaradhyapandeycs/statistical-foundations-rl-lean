import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Private uncompiled exact-factor inversion for empirical standard
deviation. No probability estimate is assumed or asserted. -/
namespace StatisticalRL.Probability

theorem empirical_std_exceedance_implies_selfbound_deviation
    (n B v z t : ℝ) (hn : 1 < n) (hB : 0 < B)
    (hv : 0 ≤ v) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hexceed : Real.sqrt v > Real.sqrt (n/(n-1)*z) + B*Real.sqrt (2*t/(n-1))) :
    Real.sqrt (2*(n/(n-1))*(n*v/B^2)*t) <
      n*v/B^2 - (n^2/((n-1)*B^2))*z := by
  let σ := Real.sqrt v
  let s := Real.sqrt (n/(n-1)*z)
  let ρ := B*Real.sqrt (2*t/(n-1))
  let k := n/B^2
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hk : 0 < k := by dsimp [k]; positivity
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hσ2 : σ^2 = v := Real.sq_sqrt hv
  have hs2 : s^2 = n/(n-1)*z := Real.sq_sqrt (by positivity)
  have hρ2 : ρ^2 = B^2*(2*t/(n-1)) := by
    dsimp [ρ]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hgap : σ*ρ < σ^2-s^2 := by
    have hpos : 0 < (σ-s-ρ)*(σ+s) := mul_pos (by linarith) (by linarith)
    have hnonneg : 0 ≤ ρ*s := mul_nonneg hρ hs
    nlinarith
  have hrad : Real.sqrt (2*(n/(n-1))*(n*v/B^2)*t) = k*σ*ρ := by
    have hl : 0 ≤ Real.sqrt (2*(n/(n-1))*(n*v/B^2)*t) := Real.sqrt_nonneg _
    have hr : 0 ≤ k*σ*ρ := by positivity
    have hl2 := Real.sq_sqrt (show 0 ≤ 2*(n/(n-1))*(n*v/B^2)*t by positivity)
    have hr2 : (k*σ*ρ)^2 = 2*(n/(n-1))*(n*v/B^2)*t := by
      rw [mul_pow, mul_pow, hσ2, hρ2]
      dsimp [k]
      field_simp
      <;> ring
    nlinarith
  rw [hrad]
  have hscaled := mul_lt_mul_of_pos_left hgap hk
  have heq : k*(σ^2-s^2) = n*v/B^2 - (n^2/((n-1)*B^2))*z := by
    rw [hσ2, hs2]
    dsimp [k]
    field_simp
    <;> ring
  rw [← heq]
  nlinarith

end StatisticalRL.Probability
