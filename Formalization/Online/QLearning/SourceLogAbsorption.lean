import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit source-log comparison in the nondegenerate regime. -/
namespace StatisticalRL.OnlineRL

theorem qLearning_source_log_absorb (x δ : ℝ) (hx : 2 ≤ x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (4*x/δ) ≤ 3*Real.log (x/δ) := by
  let y := x/δ
  have hy : 2 ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ hδ]
    nlinarith
  have hy0 : 0 < y := by linarith
  have hy2 : 4 ≤ y^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hy2 hy0.le
  have hpow : 4*y ≤ y^3 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 4*y) hpow
  rw [Real.log_pow] at hlog
  have he : 4*x/δ = 4*y := by dsimp [y]; ring
  rw [he]
  exact hlog
end StatisticalRL.OnlineRL
