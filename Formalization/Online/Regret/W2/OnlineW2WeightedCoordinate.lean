import Formalization.Probability.Variance
import Mathlib.Data.Real.Sqrt

/-! Deterministic weighted coordinate-error step for the adaptive W₂ source
term. A coordinate certificate is an intermediate input; this file does not
assert its probability or a source W₂ bound. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State : Type*} [Fintype State]

/-- Pointwise coordinate errors control an adaptive bounded continuation via
centering and Cauchy–Schwarz, without requiring its independence from q. -/
theorem onlineW2_weighted_coordinate_bound
    (p q : FiniteDistribution State) (V : State → ℝ) (H L N : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hN : 0 < N)
    (hV : ∀ x, 0 ≤ V x ∧ V x ≤ H)
    (hcoord : ∀ x, |q.prob x - p.prob x| ≤
      Real.sqrt (2 * p.prob x * L / N) + L / N) :
    q.expectation V - p.expectation V ≤
      Real.sqrt (2 * (Fintype.card State : ℝ) * L / N) * Real.sqrt (p.variance V) +
      (Fintype.card State : ℝ) * H * L / N := by
  classical
  let m := p.expectation V
  let z : State → ℝ := fun x => V x - m
  have hm0 : 0 ≤ m := p.expectation_nonneg (fun x => (hV x).1)
  have hmH : m ≤ H := p.expectation_le_const (fun x => (hV x).2)
  have hz (x : State) : |z x| ≤ H := by
    apply abs_le.mpr
    dsimp [z]
    constructor <;> linarith [(hV x).1, (hV x).2]
  have hcenter : q.expectation V - p.expectation V =
      ∑ x, (q.prob x - p.prob x) * z x := by
    have he : (fun x => (q.prob x - p.prob x) * z x) =
        fun x => (q.prob x * V x - p.prob x * V x) - (q.prob x - p.prob x) * m := by
      funext x
      dsimp [z]
      ring
    rw [he, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_sub_distrib, q.sum_prob, p.sum_prob]
    simp only [sub_self, zero_mul, sub_zero]
    rfl
  rw [hcenter]
  calc
    _ ≤ ∑ x, |q.prob x - p.prob x| * |z x| := by
      apply Finset.sum_le_sum
      intro x hx
      exact (le_abs_self _).trans_eq (abs_mul _ _)
    _ ≤ ∑ x, (Real.sqrt (2 * p.prob x * L / N) + L / N) * |z x| := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hcoord x) (abs_nonneg _)
    _ = (∑ x, Real.sqrt (2 * p.prob x * L / N) * |z x|) +
        (L / N) * (∑ x, |z x|) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.sqrt (2 * (Fintype.card State : ℝ) * L / N) * Real.sqrt (p.variance V) +
        (Fintype.card State : ℝ) * H * L / N := by
      have hbound : (∑ x, |z x|) ≤ (Fintype.card State : ℝ) * H := by
        calc
          _ ≤ ∑ _x : State, H := Finset.sum_le_sum (fun x _ => hz x)
          _ = _ := by simp
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun _ : State => (1 : ℝ)) (fun x => Real.sqrt (p.prob x) * |z x|)
      have hweighted : (∑ x, (Real.sqrt (p.prob x) * |z x|)^2) = p.variance V := by
        rw [p.variance_eq_expectation_centered_sq]
        unfold FiniteDistribution.expectation
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_pow, Real.sq_sqrt (p.prob_nonneg x), sq_abs]
        rfl
      have hcs' : (∑ x, Real.sqrt (p.prob x) * |z x|) ≤
          Real.sqrt (Fintype.card State : ℝ) * Real.sqrt (p.variance V) := by
        simpa [hweighted] using hcs
      have hfactor (x : State) : Real.sqrt (2 * p.prob x * L / N) =
          Real.sqrt (2 * L / N) * Real.sqrt (p.prob x) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * L / N)]
        congr 1
        ring
      have hmain : (∑ x, Real.sqrt (2 * p.prob x * L / N) * |z x|) ≤
          Real.sqrt (2 * (Fintype.card State : ℝ) * L / N) * Real.sqrt (p.variance V) := by
        have hh := mul_le_mul_of_nonneg_left hcs' (Real.sqrt_nonneg (2 * L / N))
        have hprod : Real.sqrt (2 * L / N) * Real.sqrt (Fintype.card State : ℝ) =
            Real.sqrt (2 * (Fintype.card State : ℝ) * L / N) := by
          rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * L / N)]
          congr 1
          ring
        calc
          _ = Real.sqrt (2 * L / N) * (∑ x, Real.sqrt (p.prob x) * |z x|) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [hfactor]
            ring
          _ ≤ Real.sqrt (2 * L / N) * (Real.sqrt (Fintype.card State : ℝ) *
              Real.sqrt (p.variance V)) := hh
          _ = _ := by rw [← hprod]; ring
      have hlin := mul_le_mul_of_nonneg_left hbound (div_nonneg hL hN.le)
      calc
        _ ≤ Real.sqrt (2 * (Fintype.card State : ℝ) * L / N) * Real.sqrt (p.variance V) +
            (L / N) * ((Fintype.card State : ℝ) * H) := add_le_add hmain hlin
        _ = _ := by ring
end StatisticalRL.OnlineRL
