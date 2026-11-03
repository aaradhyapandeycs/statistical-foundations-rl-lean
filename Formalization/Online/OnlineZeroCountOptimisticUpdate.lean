import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Proposed source correction for the undefined UCBVI zero-visit update.
Unvisited rows retain the optimistic cap H; positive visits use the exact
printed Bernstein backup. This makes the missing N=0 branch explicit. It is a
proposal, not an author-approved erratum or a completed algorithm theorem. -/
namespace StatisticalRL.OnlineRL

/-- Total source-compatible scalar Q update: no zero-count bonus is evaluated.
The empirical row can retain its source uniform initialization when N=0. -/
noncomputable def onlineZeroCountSafeQUpdate
    (reward mean variance H L c₁ c₂ : ℝ) (N : ℕ) : ℝ :=
  if N=0 then H else
    min (reward+mean+c₁*Real.sqrt (variance*L/N)+c₂*H*L/N) H

/-- The explicit unvisited branch agrees with the source's intended optimistic
Case1, without interpreting real division by zero as an infinite bonus. -/
theorem onlineZeroCountSafeQUpdate_zero
    (reward mean variance H L c₁ c₂ : ℝ) :
    onlineZeroCountSafeQUpdate reward mean variance H L c₁ c₂ 0=H := by
  simp [onlineZeroCountSafeQUpdate]

/-- Every positive-count update is exactly the printed algorithm formula. -/
theorem onlineZeroCountSafeQUpdate_positive
    (reward mean variance H L c₁ c₂ : ℝ) (N : ℕ) (hN : 0<N) :
    onlineZeroCountSafeQUpdate reward mean variance H L c₁ c₂ N =
      min (reward+mean+c₁*Real.sqrt (variance*L/N)+c₂*H*L/N) H := by
  simp [onlineZeroCountSafeQUpdate,Nat.ne_of_gt hN]

/-- The source small-count saturation follows deterministically for N=1,2.
No stochastic concentration is spent, and the zero-count branch is explicit. -/
theorem onlineZeroCountSafeQUpdate_small
    (reward mean variance H L c₁ c₂ : ℝ) (N : ℕ) (hN : N≤2)
    (hr : 0≤reward) (hm : 0≤mean) (hH : 0≤H) (hL : 1≤L)
    (hc₁ : 0≤c₁) (hc₂ : 2≤c₂) :
    onlineZeroCountSafeQUpdate reward mean variance H L c₁ c₂ N=H := by
  by_cases hz : N=0
  · subst N
    exact onlineZeroCountSafeQUpdate_zero _ _ _ _ _ _ _
  · have hn : 0<(N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hn2 : (N : ℝ)≤2 := by exact_mod_cast hN
    have hc2H := mul_le_mul_of_nonneg_right hc₂ hH
    have hLprod := mul_le_mul_of_nonneg_left hL
      (mul_nonneg (by linarith : 0≤c₂) hH)
    have hlinear : H≤c₂*H*L/N := by
      apply (le_div_iff₀ hn).2
      have hNprod := mul_le_mul_of_nonneg_left hn2 hH
      nlinarith [hc2H,hLprod,hNprod]
    have hsqrt : 0≤c₁*Real.sqrt (variance*L/N) :=
      mul_nonneg hc₁ (Real.sqrt_nonneg _)
    simp only [onlineZeroCountSafeQUpdate,if_neg hz]
    exact min_eq_right (by linarith)

/-- The repaired update always stays in the source interval[0,H] from
nonnegative actual reward/empirical mean/bonus coefficients. -/
theorem onlineZeroCountSafeQUpdate_range
    (reward mean variance H L c₁ c₂ : ℝ) (N : ℕ)
    (hr : 0≤reward) (hm : 0≤mean) (hH : 0≤H)
    (hL : 0≤L) (hc₁ : 0≤c₁) (hc₂ : 0≤c₂) :
    0≤onlineZeroCountSafeQUpdate reward mean variance H L c₁ c₂ N ∧
      onlineZeroCountSafeQUpdate reward mean variance H L c₁ c₂ N≤H := by
  unfold onlineZeroCountSafeQUpdate
  split_ifs
  · exact ⟨hH,le_rfl⟩
  · have hraw : 0≤reward+mean+c₁*Real.sqrt (variance*L/N)+c₂*H*L/N := by positivity
    exact ⟨le_min hraw hH,min_le_right _ _⟩

/-- The actual source confidence allocation is far inside the range needed
for deterministic saturation: delta'≤1/100 implies log(1/delta')≥1. -/
theorem onlineSmallConfidence_log_ge_one
    (δ : ℝ) (hδ : 0<δ) (hδsmall : δ≤1/100) :
    1≤Real.log (1/δ) := by
  have hlog2 : (1/2 : ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h ⊢
    exact h
  have hfour : (4 : ℝ)≤1/δ := (le_div_iff₀ hδ).2 (by linarith)
  have hlog4 : (1 : ℝ)≤Real.log 4 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
    linarith
  exact hlog4.trans (Real.log_le_log (by norm_num : (0 : ℝ)<4) hfour)

end StatisticalRL.OnlineRL
