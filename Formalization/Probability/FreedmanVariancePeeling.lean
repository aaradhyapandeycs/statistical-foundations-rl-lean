import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Deterministic dyadic variance bins for source `lem:Freedman-prelim`.
This file proves no probabilistic martingale tail inequality. -/
namespace StatisticalRL

/-- Splitting a variance scale once shifts the dyadic exponent exactly. -/
theorem dyadic_variance_div_step (v : ℝ) (j : ℕ) :
    (v / 2) / (2 : ℝ) ^ j = v / (2 : ℝ) ^ (j + 1) := by
  rw [div_div, pow_succ]
  congr 1
  ring

/-- K dyadic upper bins cover every variance w∈[0,v]. The chosen bin
upper endpoint is at most twice max(w,v/2^K), including zero variance and
all bin boundaries. This is the deterministic peeling step for the source
random-variance Freedman radius; no tail bound is assumed here. -/
theorem dyadic_variance_bin_cover (K : ℕ) (hK : 0 < K)
    (v w : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) (hwv : w ≤ v) :
    ∃ j : ℕ, j < K ∧ w ≤ v / (2 : ℝ) ^ j ∧
      v / (2 : ℝ) ^ j ≤ 2 * max w (v / (2 : ℝ) ^ K) := by
  induction K generalizing v w with
  | zero => omega
  | succ K ih =>
    by_cases hzero : K = 0
    · subst K
      refine ⟨0, by omega, ?_, ?_⟩
      · simpa using hwv
      · have hm := le_max_right w (v / 2)
        norm_num only [pow_zero, pow_one, div_one]
        linarith
    · by_cases htop : v / 2 ≤ w
      · refine ⟨0, by omega, ?_, ?_⟩
        · simpa using hwv
        · have hm := le_max_left w (v / (2 : ℝ) ^ (K + 1))
          norm_num only [pow_zero, div_one]
          linarith
      · obtain ⟨j, hj, hlow, hupp⟩ := ih (by omega) (v / 2) w
          (by positivity) hw (le_of_lt (not_le.mp htop))
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · simpa only [dyadic_variance_div_step] using hlow
        · simpa only [dyadic_variance_div_step] using hupp

/-- The bin comparison gives the exact factor-eight variance radius used
in the source. This remains a deterministic square-root comparison. -/
theorem dyadic_variance_radius_cover (K : ℕ) (hK : 0 < K)
    (v w L : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) (hwv : w ≤ v) (hL : 0 ≤ L) :
    ∃ j : ℕ, j < K ∧ w ≤ v / (2 : ℝ) ^ j ∧
      Real.sqrt (4 * (v / (2 : ℝ) ^ j) * L) ≤
        Real.sqrt (8 * max w (v / (2 : ℝ) ^ K) * L) := by
  obtain ⟨j, hj, hlo, hhi⟩ := dyadic_variance_bin_cover K hK v w hv hw hwv
  refine ⟨j, hj, hlo, Real.sqrt_le_sqrt ?_⟩
  have hm := mul_le_mul_of_nonneg_right hhi hL
  nlinarith

end StatisticalRL
