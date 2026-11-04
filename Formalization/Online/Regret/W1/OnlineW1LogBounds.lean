import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! OnlineW1LogBounds: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL

/-- A finite visit-count harmonic envelope is bounded by 4 log₂ K for K≥2. -/
theorem onlineW1_logEnvelope_le (K : ℕ) (hK : 2 ≤ K) :
    1 + Real.log (K + 1 : ℝ) ≤ 4 * (Real.log K / Real.log 2) := by
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0 : ℝ) < K := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hl2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hl : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hk
  have hlpos : 0 ≤ Real.log K := by linarith
  have hpoly : (K + 1 : ℝ) ≤ (K : ℝ)^2 := by nlinarith
  have hp : (0 : ℝ) < K + 1 := by linarith
  have hlog := Real.log_le_log hp hpoly
  rw [Real.log_pow] at hlog
  have hdiv : Real.log K ≤ Real.log K / Real.log 2 := by
    apply (le_div_iff₀ hl2).2
    nlinarith
  norm_num at hlog
  have hhalf : (1 : ℝ) ≤ 2 * Real.log K := by linarith
  linarith
end StatisticalRL.OnlineRL
