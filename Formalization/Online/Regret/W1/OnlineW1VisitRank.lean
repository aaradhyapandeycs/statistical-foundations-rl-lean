import Formalization.Online.SourceOptimism.VisitCountFoundation
import Mathlib.NumberTheory.Harmonic.Bounds

/-! OnlineW1VisitRank: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Every actual visit to a fixed row encounters counts 0,1,...,N−1 exactly
once. Valid for every realized adaptive visit sequence. -/
theorem onlineVisitCount_sum_by_rank {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (r : Row) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r then f (onlineVisitCount rowAt j r) else 0) =
      ∑ n ∈ Finset.range (onlineVisitCount rowAt K r), f n := by
  classical
  induction K with
  | zero => simp [onlineVisitCount_zero]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, onlineVisitCount_succ]
      by_cases hr : rowAt K = r
      · simp [hr, Finset.sum_range_succ]
      · simp [hr]

/-- Positive-count bonuses are summed without evaluating their first-visit
zero denominator. The missing first visit is a separate source convention. -/
theorem onlineVisitCount_positive_sum_by_rank {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (r : Row) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ 0 < onlineVisitCount rowAt j r
        then f (onlineVisitCount rowAt j r) else 0) =
      ∑ n ∈ Finset.range (onlineVisitCount rowAt K r), if 0 < n then f n else 0 := by
  have h := onlineVisitCount_sum_by_rank rowAt K r (fun n => if 0 < n then f n else 0)
  simpa only [ite_and] using h

/-- Reciprocal positive pre-visit counts have the usual harmonic budget.
The right-side log concerns only the deterministic final visit count; it is
not an exploration-bonus definition at zero visits. -/
theorem onlineVisitCount_reciprocal_sum_le {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (r : Row) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ 0 < onlineVisitCount rowAt j r
        then (onlineVisitCount rowAt j r : ℝ)⁻¹ else 0) ≤
      1 + Real.log (onlineVisitCount rowAt K r : ℝ) := by
  classical
  rw [onlineVisitCount_positive_sum_by_rank rowAt K r (fun n => (n : ℝ)⁻¹)]
  let N := onlineVisitCount rowAt K r
  have hf (n : ℕ) : (if 0 < n then (n : ℝ)⁻¹ else 0) = (n : ℝ)⁻¹ := by
    cases n <;> simp
  simp_rw [hf]
  have hmono : (∑ n ∈ Finset.range N, (n : ℝ)⁻¹) ≤
      ∑ n ∈ Finset.range (N + 1), (n : ℝ)⁻¹ := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hsum : (∑ n ∈ Finset.range (N + 1), (n : ℝ)⁻¹) = (harmonic N : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, inv_zero, add_zero, harmonic, Rat.cast_sum,
      Rat.cast_inv, Rat.cast_natCast]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ)⁻¹ := hmono
    _ = (harmonic N : ℝ) := hsum
    _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N

end StatisticalRL.OnlineRL
