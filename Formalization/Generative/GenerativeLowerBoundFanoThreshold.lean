import Formalization.Generative.GenerativeLowerBoundFamilyFano

/-! Explicit large-family Fano numerical threshold. -/
namespace StatisticalRL.GenerativeLowerBound

/-- For at least four hypotheses, the quarter-log KL budget gives a
one-quarter average testing lower bound. -/
theorem fano_large_cardinality_quarter (K B : ℝ) (hK : 4 ≤ K)
    (hB : B ≤ Real.log K / 4) :
    (1 : ℝ) / 4 ≤ 1 - (B + Real.log 2) / Real.log K := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl : 0 < Real.log K := Real.log_pos (by linarith)
  have h4 : Real.log 4 ≤ Real.log K := Real.log_le_log (by norm_num) hK
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at h ⊢
    linarith
  rw [hlog4] at h4
  apply (le_sub_iff_add_le).mpr
  have hd : (B + Real.log 2) / Real.log K ≤ (3 : ℝ) / 4 := by
    apply (div_le_iff₀ hl).2
    linarith
  linarith

end StatisticalRL.GenerativeLowerBound
