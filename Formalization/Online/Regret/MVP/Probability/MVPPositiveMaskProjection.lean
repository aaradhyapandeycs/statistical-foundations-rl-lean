import Formalization.Online.Regret.MVP.Probability.MVPMaskedSum
import Mathlib.Tactic

/-! Select positive rows only after every fixed-mask event holds. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_positiveParts_of_fixedMaskBounds {Row : Type*} [DecidableEq Row]
    (rows : Finset Row) (x variance : Row → ℝ) (n floor L linear : ℝ)
    (hn : 0 < n) (hL : 0 ≤ L) (hv : ∀ r ∈ rows, 0 ≤ variance r)
    (hmask : ∀ t : Finset Row, t ⊆ rows →
      |∑ r ∈ t, x r| ≤
        (Real.sqrt (8 * max (n * ∑ r ∈ t, variance r) floor * L) + linear) / n) :
    (∑ r ∈ rows, max (x r) 0) ≤
      (Real.sqrt (8 * max (n * ∑ r ∈ rows, variance r) floor * L) + linear) / n := by
  rw [mvp_sum_max_eq_positive_subset]
  let t := rows.filter (fun r => 0 < x r)
  have ht : t ⊆ rows := Finset.filter_subset _ _
  have hsum : (∑ r ∈ t, variance r) ≤ ∑ r ∈ rows, variance r :=
    Finset.sum_le_sum_of_subset_of_nonneg ht (fun r hr _ => hv r hr)
  have harg : 8 * max (n * ∑ r ∈ t, variance r) floor * L ≤
      8 * max (n * ∑ r ∈ rows, variance r) floor * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
    exact max_le_max (mul_le_mul_of_nonneg_left hsum hn.le) le_rfl
  exact (le_abs_self _).trans ((hmask t ht).trans
    (div_le_div_of_nonneg_right (add_le_add (Real.sqrt_le_sqrt harg) (le_refl linear)) hn.le))
end StatisticalRL.OnlineRL
