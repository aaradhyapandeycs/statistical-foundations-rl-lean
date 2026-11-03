import Formalization.ModelFree.QLearningRobustComparator
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Q-comparison-facts (i), support-aware upper deviation.
The nominal zero-support restriction is essential. No lower witness or robust
fixed-point comparison is claimed here. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State : Type*} [Fintype State]

/-- Zero nominal atoms contribute nothing to the centered signed deviation. -/
theorem qChi_centered_support_sum (p q : FiniteDistribution State) (v : State → ℝ)
    (hs : ∀ x, p.prob x = 0 → q.prob x = 0) :
    (∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x),
      (q.prob x - p.prob x) * (v x - p.expectation v)) = q.expectation v - p.expectation v := by
  classical
  have he : (∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x),
      (q.prob x - p.prob x) * (v x - p.expectation v)) =
      ∑ x, (q.prob x - p.prob x) * (v x - p.expectation v) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hz : p.prob x = 0 := by
      have hn : ¬ 0 < p.prob x := by simpa using hnot
      exact le_antisymm (le_of_not_gt hn) (p.prob_nonneg x)
    simp [hz, hs x hz]
  rw [he]
  have hx : (fun x ↦ (q.prob x - p.prob x) * (v x - p.expectation v)) =
      fun x ↦ q.prob x * v x - p.prob x * v x -
        q.prob x * p.expectation v + p.prob x * p.expectation v := by
    funext x; ring
  simp only [hx, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    q.sum_prob, p.sum_prob, one_mul]
  change q.expectation v - p.expectation v - p.expectation v + p.expectation v = q.expectation v - p.expectation v
  ring

/-- The support-aware finite Cauchy–Schwarz bound, with actual nominal variance. -/
theorem qChi_expectation_sub_sq_le (p q : FiniteDistribution State) (v : State → ℝ)
    (hs : ∀ x, p.prob x = 0 → q.prob x = 0) :
    (q.expectation v - p.expectation v) ^ 2 ≤ qChiSquared p q * p.variance v := by
  classical
  let S := Finset.univ.filter (fun x ↦ 0 < p.prob x)
  have hv : (∑ x ∈ S, p.prob x * (v x - p.expectation v) ^ 2) = p.variance v := by
    rw [p.variance_eq_expectation_centered_sq, FiniteDistribution.expectation]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hz : p.prob x = 0 := by
      have hn : ¬ 0 < p.prob x := by simpa [S] using hnot
      exact le_antisymm (le_of_not_gt hn) (p.prob_nonneg x)
    simp [hz]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    (r := fun x ↦ (q.prob x - p.prob x) * (v x - p.expectation v))
    (f := fun x ↦ (q.prob x - p.prob x) ^ 2 / p.prob x)
    (g := fun x ↦ p.prob x * (v x - p.expectation v) ^ 2)
    (fun x hx ↦ div_nonneg (sq_nonneg _) (p.prob_nonneg x))
    (fun x hx ↦ mul_nonneg (p.prob_nonneg x) (sq_nonneg _))
    (by
      intro x hx
      have hp : p.prob x ≠ 0 := ne_of_gt (Finset.mem_filter.mp hx).2
      field_simp)
  rw [hv] at hc
  simpa only [S, qChi_centered_support_sum p q v hs, qChiSquared] using hc

/-- No span or boundedness premise is needed for this one-sided part of the
source support-function bound: every real finite value vector is allowed. -/
theorem qChi_abs_expectation_sub_le (p q : FiniteDistribution State) (v : State → ℝ)
    (hs : ∀ x, p.prob x = 0 → q.prob x = 0) :
    |q.expectation v - p.expectation v| ≤ Real.sqrt (qChiSquared p q * p.variance v) := by
  have hχ : 0 ≤ qChiSquared p q := by
    unfold qChiSquared
    exact Finset.sum_nonneg fun x hx ↦ div_nonneg (sq_nonneg _) (p.prob_nonneg x)
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg hχ (p.variance_nonneg v))).2
  simpa only [sq_abs] using qChi_expectation_sub_sq_le p q v hs

/-- Every feasible row satisfies the source upper radius, including rho=0
and zero variance. The stronger endpoint causes no source restriction. -/
theorem qChiBall_abs_expectation_sub_le (p q : FiniteDistribution State) (ρ : ℝ)
    (v : State → ℝ) (hq : q ∈ qChiBall p ρ) :
    |q.expectation v - p.expectation v| ≤ Real.sqrt (ρ * p.variance v) := by
  exact (qChi_abs_expectation_sub_le p q v hq.1).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hq.2 (p.variance_nonneg v)))

/-- Source robust supremum upper deviation, before its separate lower witness. -/
theorem qRobustExpectations_sSup_sub_le (p : FiniteDistribution State) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (v : State → ℝ) :
    sSup (qRobustExpectations p ρ v) - p.expectation v ≤ Real.sqrt (ρ * p.variance v) := by
  have hb : sSup (qRobustExpectations p ρ v) ≤ p.expectation v + Real.sqrt (ρ * p.variance v) := by
    apply csSup_le (qRobustExpectations_nonempty p ρ hρ v)
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hz
    have hh := (le_abs_self (q.expectation v - p.expectation v)).trans
      (qChiBall_abs_expectation_sub_le p q ρ v hq)
    linarith
  linarith

end StatisticalRL.QLearning
