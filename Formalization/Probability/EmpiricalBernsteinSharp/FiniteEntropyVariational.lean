import Formalization.Probability.EmpiricalBernsteinSharp.FinitePositiveLogSum

/-! Private uncompiled finite entropy variational estimate. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

/-- The entropy of a positive function is bounded by its relative entropy
against any positive constant. Probability weights may vanish. -/
theorem finite_entropy_le_relative_constant {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (c : ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hf : ∀ i, 0 < f i) (hc : 0 < c) :
    (∑ i, p i*(f i*Real.log (f i))) -
        (∑ i, p i*f i)*Real.log (∑ i, p i*f i) ≤
      ∑ i, p i*(f i*Real.log (f i/c) - f i + c) := by
  let m := ∑ i, p i*f i
  have hex : ∃ i, 0 < p i := by
    by_contra h
    push_neg at h
    have hs : (∑ i, p i) ≤ 0 := Finset.sum_nonpos (fun i _ ↦ h i)
    linarith
  obtain ⟨j, hj⟩ := hex
  have hm : 0 < m := by
    apply Finset.sum_pos' (fun i _ ↦ mul_nonneg (hp i) (hf i).le)
    exact ⟨j, Finset.mem_univ _, mul_pos hj (hf j)⟩
  have hlog := Real.log_le_sub_one_of_pos (div_pos hc hm)
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt hm)] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hm.le
  have hratio : m*(c/m-1) = c-m := by field_simp
  rw [hratio] at hscaled
  simp_rw [Real.log_div (ne_of_gt (hf _)) (ne_of_gt hc)]
  simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hp1, one_mul]
  have hsum : (∑ i, p i*(f i*Real.log c)) = m*Real.log c := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  rw [hsum]
  dsimp [m] at hscaled ⊢
  nlinarith

end StatisticalRL.EmpiricalBernsteinEntropy
