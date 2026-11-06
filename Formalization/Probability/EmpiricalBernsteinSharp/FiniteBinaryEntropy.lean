import Formalization.Probability.EmpiricalBernsteinSharp.FinitePositiveLogSum

/-! Private uncompiled binary entropy convexity for finite probability weights.
The product tensorization induction and concentration argument remain open. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

/-- Averaging over the first coordinate cannot increase the entropy in the
second coordinate. Both sets of weights may contain zeros. -/
theorem finite_binary_entropy_convexity {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (g : α → β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ y, q y = 1)
    (hg : ∀ x y, 0 < g x y) :
    (∑ y, q y * ((∑ x, p x*g x y) *
      Real.log ((∑ x, p x*g x y) / (∑ x, p x*(∑ y, q y*g x y))))) ≤
    ∑ x, p x * (∑ y, q y * (g x y *
      Real.log (g x y / (∑ y, q y*g x y)))) := by
  let m : α → ℝ := fun x ↦ ∑ y, q y*g x y
  have hqpos : ∃ y, 0 < q y := by
    by_contra h
    push_neg at h
    have hs : (∑ y, q y) ≤ 0 := Finset.sum_nonpos (fun y _ ↦ h y)
    linarith
  obtain ⟨y₀, hy₀⟩ := hqpos
  have hm (x : α) : 0 < m x := by
    dsimp [m]
    apply Finset.sum_pos' (fun y _ ↦ mul_nonneg (hq y) (hg x y).le)
    exact ⟨y₀, Finset.mem_univ _, mul_pos hy₀ (hg x y₀)⟩
  have hpoint (y : β) := finite_weighted_positive_logsum p (fun x ↦ g x y) m
    hp hp1 (fun x ↦ hg x y) hm
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (hpoint y) (hq y))
  calc
    _ ≤ ∑ y, q y * (∑ x, p x*g x y * Real.log (g x y / m x)) := hsum
    _ = ∑ x, p x * (∑ y, q y * (g x y * Real.log (g x y / m x))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := rfl

end StatisticalRL.EmpiricalBernsteinEntropy
