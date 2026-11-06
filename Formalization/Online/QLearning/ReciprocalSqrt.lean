import Formalization.Online.QLearning.VisitShift
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The source reciprocal-square-root aggregation, including N=0. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_reciprocalSqrt_step (n : ℕ) :
    1 / Real.sqrt ((n+1:ℕ):ℝ) ≤
      2*(Real.sqrt ((n+1:ℕ):ℝ)-Real.sqrt (n:ℝ)) := by
  have hn : (0:ℝ) ≤ n := by positivity
  have hn1 : (0:ℝ) < (n+1:ℕ) := by positivity
  have ha : 0 < Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr hn1
  have hb : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have hs1 := Real.sq_sqrt hn1.le
  have hs0 := Real.sq_sqrt hn
  have hsq := sq_nonneg (Real.sqrt ((n+1:ℕ):ℝ)-Real.sqrt (n:ℝ))
  rw [div_le_iff₀ ha]
  push_cast at hs1 ⊢
  nlinarith

theorem qLearning_sum_reciprocalSqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (n:ℝ)) ≤ 2*Real.sqrt (N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
    have hstep := qLearning_reciprocalSqrt_step N
    push_cast at ih hstep ⊢
    linarith
end StatisticalRL.OnlineRL
