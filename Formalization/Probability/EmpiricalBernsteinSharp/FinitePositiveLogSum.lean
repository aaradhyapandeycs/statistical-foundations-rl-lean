import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Private uncompiled log-sum prerequisite for entropy tensorization.
The function values are positive, while probability weights may vanish. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_weighted_log_le {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 < x i)
    (hw1 : ∑ i, w i = 1) :
    (∑ i, w i * Real.log (x i)) ≤ Real.log (∑ i, w i * x i) := by
  let m := ∑ i, w i * x i
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hs : (∑ i, w i) ≤ 0 := Finset.sum_nonpos (fun i _ ↦ h i)
    linarith
  obtain ⟨j, hj⟩ := hex
  have hm : 0 < m := by
    apply Finset.sum_pos' (fun i _ ↦ mul_nonneg (hw i) (hx i).le)
    exact ⟨j, Finset.mem_univ _, mul_pos hj (hx j)⟩
  have hp (i : ι) : w i * (Real.log (x i) - Real.log m) ≤
      w i * (x i / m - 1) := by
    have ht := Real.log_le_sub_one_of_pos (div_pos (hx i) hm)
    rw [Real.log_div (ne_of_gt (hx i)) (ne_of_gt hm)] at ht
    exact mul_le_mul_of_nonneg_left ht (hw i)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hp i)
  have hr : (∑ i, w i * (x i / m - 1)) = 0 := by
    simp_rw [mul_sub, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [mul_one, hw1]
    change m / m - 1 = 0
    rw [div_self (ne_of_gt hm)]
    ring
  have hl : (∑ i, w i * (Real.log (x i) - Real.log m)) =
      (∑ i, w i * Real.log (x i)) - Real.log m := by
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]
  rw [hl, hr] at hh
  linarith

/-- Log-sum with nonnegative probability weights and strictly positive
function values, without logarithms of the weights. -/
theorem finite_weighted_positive_logsum {ι : Type*} [Fintype ι]
    (p g m : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hg : ∀ i, 0 < g i) (hm : ∀ i, 0 < m i) :
    (∑ i, p i*g i) * Real.log ((∑ i, p i*g i)/(∑ i, p i*m i)) ≤
      ∑ i, p i*g i * Real.log (g i/m i) := by
  let A := ∑ i, p i*g i
  let M := ∑ i, p i*m i
  have hpos : ∃ i, 0 < p i := by
    by_contra h
    push_neg at h
    have hs : (∑ i, p i) ≤ 0 := Finset.sum_nonpos (fun i _ ↦ h i)
    linarith
  obtain ⟨j, hj⟩ := hpos
  have hA : 0 < A := by
    apply Finset.sum_pos' (fun i _ ↦ mul_nonneg (hp i) (hg i).le)
    exact ⟨j, Finset.mem_univ _, mul_pos hj (hg j)⟩
  have hM : 0 < M := by
    apply Finset.sum_pos' (fun i _ ↦ mul_nonneg (hp i) (hm i).le)
    exact ⟨j, Finset.mem_univ _, mul_pos hj (hm j)⟩
  let w : ι → ℝ := fun i ↦ p i*g i/A
  let x : ι → ℝ := fun i ↦ m i/g i
  have hw : ∀ i, 0 ≤ w i := fun i ↦ div_nonneg (mul_nonneg (hp i) (hg i).le) hA.le
  have hx : ∀ i, 0 < x i := fun i ↦ div_pos (hm i) (hg i)
  have hw1 : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hA)
  have hmean : (∑ i, w i*x i) = M/A := by
    dsimp [w, x]
    have hi (i : ι) : p i*g i/A*(m i/g i) = p i*m i/A := by
      field_simp [ne_of_gt (hg i)]
    simp_rw [hi, ← Finset.sum_div]
    rfl
  have hterm (i : ι) : w i * Real.log (x i) =
      -(p i*g i*Real.log (g i/m i))/A := by
    dsimp [w, x]
    rw [Real.log_div (ne_of_gt (hm i)) (ne_of_gt (hg i)),
      Real.log_div (ne_of_gt (hg i)) (ne_of_gt (hm i))]
    ring
  have hj := finite_weighted_log_le w x hw hx hw1
  rw [hmean] at hj
  simp_rw [hterm] at hj
  rw [← Finset.sum_div, Finset.sum_neg_distrib] at hj
  have hlog : Real.log (M/A) = -Real.log (A/M) := by
    rw [Real.log_div (ne_of_gt hM) (ne_of_gt hA),
      Real.log_div (ne_of_gt hA) (ne_of_gt hM)]
    ring
  rw [hlog] at hj
  have hh := mul_le_mul_of_nonneg_left hj hA.le
  field_simp at hh
  nlinarith

end StatisticalRL.EmpiricalBernsteinEntropy
