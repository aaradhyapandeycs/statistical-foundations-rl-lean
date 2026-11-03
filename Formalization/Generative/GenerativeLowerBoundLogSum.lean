import Formalization.Generative.GenerativeLowerBoundWeightedLog

/-! Strict-positive finite log-sum inequality, a bounded Fano ingredient. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Finite log-sum inequality for strictly positive inputs. Empty/zero cells
need a separate extension before this can prove full Fano/data processing. -/
theorem finite_positive_logSum {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  let A := ∑ i, a i
  let B := ∑ i, b i
  have hA : 0 < A := Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have hB : 0 < B := Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  let w : ι → ℝ := fun i ↦ a i / A
  let x : ι → ℝ := fun i ↦ b i / a i
  have hw : ∀ i, 0 < w i := fun i ↦ div_pos (ha i) hA
  have hx : ∀ i, 0 < x i := fun i ↦ div_pos (hb i) (ha i)
  have hw1 : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    change A / A = 1
    exact div_self (ne_of_gt hA)
  have hmean : (∑ i, w i * x i) = B / A := by
    dsimp [w, x]
    have hi (i : ι) : a i / A * (b i / a i) = b i / A := by
      field_simp [ne_of_gt (ha i)]
    simp_rw [hi, ← Finset.sum_div]
    rfl
  have hterm (i : ι) : w i * Real.log (x i) =
      -(a i * Real.log (a i / b i)) / A := by
    dsimp [w, x]
    rw [Real.log_div (ne_of_gt (hb i)) (ne_of_gt (ha i)),
      Real.log_div (ne_of_gt (ha i)) (ne_of_gt (hb i))]
    ring
  have hj := finite_weighted_log_le_log_sum w x hw hx hw1
  rw [hmean] at hj
  simp_rw [hterm] at hj
  rw [← Finset.sum_div, Finset.sum_neg_distrib] at hj
  have hlog : Real.log (B / A) = -Real.log (A / B) := by
    rw [Real.log_div (ne_of_gt hB) (ne_of_gt hA), Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
    ring
  rw [hlog] at hj
  have hm := mul_le_mul_of_nonneg_left hj hA.le
  field_simp at hm
  nlinarith

end StatisticalRL.GenerativeLowerBound
