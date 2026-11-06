import Formalization.Probability.EmpiricalBernsteinSharp.FiniteBinaryEntropy

/-! Private uncompiled positive-function binary entropy tensorization. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_binary_entropy_tensorization {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (g : α → β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ y, q y = 1)
    (hg : ∀ x y, 0 < g x y) :
    (∑ x, p x * (∑ y, q y * (g x y * Real.log (g x y)))) -
        (∑ x, p x * (∑ y, q y*g x y)) *
          Real.log (∑ x, p x * (∑ y, q y*g x y)) ≤
      (∑ y, q y * ((∑ x, p x*(g x y*Real.log (g x y))) -
        (∑ x, p x*g x y)*Real.log (∑ x, p x*g x y))) +
      (∑ x, p x * ((∑ y, q y*(g x y*Real.log (g x y))) -
        (∑ y, q y*g x y)*Real.log (∑ y, q y*g x y))) := by
  let A : β → ℝ := fun y ↦ ∑ x, p x*g x y
  let M : α → ℝ := fun x ↦ ∑ y, q y*g x y
  let Z : ℝ := ∑ x, p x*M x
  have hpEx : ∃ x, 0 < p x := by
    by_contra h
    push_neg at h
    have hs : (∑ x, p x) ≤ 0 := Finset.sum_nonpos (fun x _ ↦ h x)
    linarith
  have hqEx : ∃ y, 0 < q y := by
    by_contra h
    push_neg at h
    have hs : (∑ y, q y) ≤ 0 := Finset.sum_nonpos (fun y _ ↦ h y)
    linarith
  obtain ⟨x₀, hx₀⟩ := hpEx
  obtain ⟨y₀, hy₀⟩ := hqEx
  have hA (y : β) : 0 < A y := by
    dsimp [A]
    apply Finset.sum_pos' (fun x _ ↦ mul_nonneg (hp x) (hg x y).le)
    exact ⟨x₀, Finset.mem_univ _, mul_pos hx₀ (hg x₀ y)⟩
  have hM (x : α) : 0 < M x := by
    dsimp [M]
    apply Finset.sum_pos' (fun y _ ↦ mul_nonneg (hq y) (hg x y).le)
    exact ⟨y₀, Finset.mem_univ _, mul_pos hy₀ (hg x y₀)⟩
  have hZ : 0 < Z := by
    dsimp [Z]
    apply Finset.sum_pos' (fun x _ ↦ mul_nonneg (hp x) (hM x).le)
    exact ⟨x₀, Finset.mem_univ _, mul_pos hx₀ (hM x₀)⟩
  have htot : (∑ y, q y*A y) = Z := by
    dsimp [A, M, Z]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hc := finite_binary_entropy_convexity p q g hp hq hp1 hq1 hg
  change (∑ y, q y*(A y*Real.log (A y/Z))) ≤
    ∑ x, p x*(∑ y, q y*(g x y*Real.log (g x y/M x))) at hc
  simp_rw [Real.log_div (ne_of_gt (hA _)) (ne_of_gt hZ)] at hc
  simp_rw [Real.log_div (ne_of_gt (hg _ _)) (ne_of_gt (hM _))] at hc
  simp only [mul_sub, Finset.sum_sub_distrib] at hc
  have hfactor1 : (∑ y, q y * (A y * Real.log Z)) = Z * Real.log Z := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, htot]
  have hfactor2 : (∑ x, p x * ∑ y, q y * (g x y * Real.log (M x))) =
      ∑ x, p x * (M x * Real.log (M x)) := by
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  rw [hfactor1, hfactor2] at hc
  change _ ≤ _
  dsimp [A, M, Z] at hc
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hc ⊢
  have hcomm : (∑ y, q y * ∑ x, p x * (g x y * Real.log (g x y))) =
      ∑ x, p x * ∑ y, q y * (g x y * Real.log (g x y)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hcomm]
  linarith

end StatisticalRL.EmpiricalBernsteinEntropy
