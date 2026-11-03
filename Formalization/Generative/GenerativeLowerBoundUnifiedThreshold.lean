import Formalization.Generative.GenerativeLowerBoundIndexGeometry
import Formalization.Generative.GenerativeLowerBoundFanoThreshold

/-! Source-style threshold arithmetic for corrected finite families. -/
namespace StatisticalRL.GenerativeLowerBound

/-- A single logarithmic budget implies the large-family Fano budget or the
small-family two-point budget. Exact family size is K=1+mn. -/
theorem correctedFamily_common_budget (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (t : ℝ) (ht : 0 ≤ t)
    (hbudget : 32768 * t ≤ Real.log ((m + 1 : ℕ) * (n + 1))) :
    (16 ≤ (m + 1) * (n + 1) ∧
      4096 * t ≤ Real.log (Fintype.card (HardFamilyIndex m n))) ∨
    ((m + 1) * (n + 1) < 16 ∧ 1024 * t ≤ 9 / 10) := by
  by_cases hsize : 16 ≤ (m + 1) * (n + 1)
  · left
    refine ⟨hsize, ?_⟩
    have hK : (4 : ℝ) ≤ Fintype.card (HardFamilyIndex m n) := by
      exact_mod_cast hardFamilyIndex_card_ge_four m n hm hn hsize
    have hS : ((m + 1 : ℕ) * (n + 1) : ℝ) ≤ 4 * Fintype.card (HardFamilyIndex m n) := by
      exact_mod_cast hardFamilyIndex_card_lower m n hm hn
    have hS0 : 0 < ((m + 1 : ℕ) * (n + 1) : ℝ) := by positivity
    have hlog := Real.log_le_log hS0 hS
    have h4K : Real.log (4 * (Fintype.card (HardFamilyIndex m n) : ℝ)) =
        Real.log 4 + Real.log (Fintype.card (HardFamilyIndex m n)) :=
      Real.log_mul (by norm_num) (by linarith)
    rw [h4K] at hlog
    have hlog4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hK
    linarith
  · right
    have hs : (m + 1) * (n + 1) < 16 := by omega
    refine ⟨hs, ?_⟩
    have hS0 : 0 < ((m + 1 : ℕ) * (n + 1) : ℝ) := by positivity
    have hS16 : ((m + 1 : ℕ) * (n + 1) : ℝ) < 16 := by exact_mod_cast hs
    have hlog := Real.log_le_sub_one_of_pos hS0
    linarith

end StatisticalRL.GenerativeLowerBound
