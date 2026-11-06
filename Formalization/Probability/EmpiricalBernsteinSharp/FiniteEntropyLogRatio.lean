import Formalization.Probability.EmpiricalBernsteinSharp.FinitePositiveLogSum

/-! Private uncompiled identity between finite entropy and its log-ratio form. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_entropy_eq_log_ratio {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hf : ∀ i, 0 < f i) :
    (∑ i, p i*(f i*Real.log (f i))) -
        (∑ i, p i*f i)*Real.log (∑ i, p i*f i) =
      ∑ i, p i*(f i*Real.log (f i/(∑ j, p j*f j))) := by
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
  change (∑ i, p i*(f i*Real.log (f i))) - m*Real.log m =
    ∑ i, p i*(f i*Real.log (f i/m))
  simp_rw [Real.log_div (ne_of_gt (hf _)) (ne_of_gt hm)]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ i, p i*(f i*Real.log m)) = m*Real.log m := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  rw [hsum]

end StatisticalRL.EmpiricalBernsteinEntropy
