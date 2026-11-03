import Formalization.Probability.Variance

/-! Finite-law pairwise variance identity and square-variance inequality. -/

open scoped BigOperators
namespace StatisticalRL.FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

/-- Pairwise-difference expression for variance under an actual finite law. -/
noncomputable def pairwiseVarianceExpression (d : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, d.prob x * d.prob y * (f x - f y) ^ 2

private theorem sum_sum_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℝ) (g : κ → ℝ) :
    (∑ i, ∑ j, f i * g j) = (∑ i, f i) * (∑ j, g j) := by
  calc
    _ = ∑ i, f i * ∑ j, g j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_mul]

/-- Pairwise finite-variance identity; zero-mass atoms are included. -/
theorem variance_eq_pairwiseVarianceExpression (d : FiniteDistribution Ω)
    (f : Ω → ℝ) :
    d.variance f = pairwiseVarianceExpression d f := by
  have hxx : (∑ x, ∑ y, d.prob x * d.prob y * f x ^ 2) =
      d.expectation (fun x ↦ f x ^ 2) := by
    calc
      _ = ∑ x, (d.prob x * f x ^ 2) * ∑ y, d.prob y := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          _ = ∑ y, (d.prob x * f x ^ 2) * d.prob y := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = _ := by simp [FiniteDistribution.expectation, d.sum_prob]
  have hyy : (∑ x, ∑ y, d.prob x * d.prob y * f y ^ 2) =
      d.expectation (fun x ↦ f x ^ 2) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ y, (d.prob y * f y ^ 2) * ∑ x, d.prob x := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          _ = ∑ x, (d.prob y * f y ^ 2) * d.prob x := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = _ := by simp [FiniteDistribution.expectation, d.sum_prob]
  have hcross : (∑ x, ∑ y, 2 * (d.prob x * f x) * (d.prob y * f y)) =
      2 * (d.expectation f) ^ 2 := by
    calc
      _ = 2 * (∑ x, ∑ y, (d.prob x * f x) * (d.prob y * f y)) := by
        calc
          _ = ∑ x, 2 * (∑ y, (d.prob x * f x) * (d.prob y * f y)) := by
            apply Finset.sum_congr rfl
            intro x hx
            calc
              _ = ∑ y, 2 * ((d.prob x * f x) * (d.prob y * f y)) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = _ := by rw [Finset.mul_sum]
          _ = _ := by rw [Finset.mul_sum]
      _ = 2 * (∑ x, d.prob x * f x) * (∑ y, d.prob y * f y) := by
        calc
          _ = 2 * ((∑ x, d.prob x * f x) * (∑ y, d.prob y * f y)) := by
            rw [sum_sum_product]
          _ = _ := by ring
      _ = _ := by
        change 2 * (d.expectation f) * d.expectation f =
          2 * (d.expectation f) ^ 2
        ring
  have hdouble :
      (∑ x, ∑ y, d.prob x * d.prob y * (f x - f y) ^ 2) =
        2 * d.expectation (fun x ↦ f x ^ 2) - 2 * (d.expectation f) ^ 2 := by
    calc
      _ = ∑ x, ∑ y,
          (d.prob x * d.prob y * f x ^ 2 -
            2 * (d.prob x * f x) * (d.prob y * f y) +
            d.prob x * d.prob y * f y ^ 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ x, ∑ y, d.prob x * d.prob y * f x ^ 2) -
          (∑ x, ∑ y, 2 * (d.prob x * f x) * (d.prob y * f y)) +
          (∑ x, ∑ y, d.prob x * d.prob y * f y ^ 2) := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by rw [hxx, hcross, hyy]; ring
  unfold pairwiseVarianceExpression FiniteDistribution.variance
  rw [hdouble]
  ring

/-- Squaring values in `[0,H]` increases variance by at most `4H²`. -/
theorem variance_sq_le_four_mul_sq (d : FiniteDistribution Ω) (U : Ω → ℝ)
    {H : ℝ} (_hH : 0 ≤ H) (hU : ∀ x, 0 ≤ U x ∧ U x ≤ H) :
    d.variance (fun x ↦ U x ^ 2) ≤ 4 * H ^ 2 * d.variance U := by
  rw [variance_eq_pairwiseVarianceExpression, variance_eq_pairwiseVarianceExpression]
  have hpoint (x y : Ω) :
      (U x ^ 2 - U y ^ 2) ^ 2 ≤ 4 * H ^ 2 * (U x - U y) ^ 2 := by
    have hx : |U x| ≤ H := by rw [abs_of_nonneg (hU x).1]; exact (hU x).2
    have hy : |U y| ≤ H := by rw [abs_of_nonneg (hU y).1]; exact (hU y).2
    have hdiff := StatisticalRL.abs_sq_sub_sq_le
      (abs_nonneg (U x - U y)) hx hy le_rfl
    have hsquare := mul_self_le_mul_self (abs_nonneg _) hdiff
    nlinarith [hsquare, sq_abs (U x - U y),
      sq_abs (U x ^ 2 - U y ^ 2)]
  have hdouble :
      (∑ x, ∑ y, d.prob x * d.prob y * (U x ^ 2 - U y ^ 2) ^ 2) ≤
        4 * H ^ 2 * (∑ x, ∑ y, d.prob x * d.prob y * (U x - U y) ^ 2) := by
    calc
      _ ≤ ∑ x, ∑ y, 4 * H ^ 2 *
          (d.prob x * d.prob y * (U x - U y) ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        have hp : 0 ≤ d.prob x * d.prob y :=
          mul_nonneg (d.prob_nonneg x) (d.prob_nonneg y)
        have hm := mul_le_mul_of_nonneg_left (hpoint x y) hp
        nlinarith [hm]
      _ = _ := by
        calc
          _ = ∑ x, ∑ y, d.prob x * d.prob y *
              (4 * H ^ 2 * (U x - U y) ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            ring
          _ = 4 * H ^ 2 *
              (∑ x, ∑ y, d.prob x * d.prob y * (U x - U y) ^ 2) := by
            calc
              _ = ∑ x, (4 * H ^ 2) *
                  (∑ y, d.prob x * d.prob y * (U x - U y) ^ 2) := by
                apply Finset.sum_congr rfl
                intro x hx
                calc
                  _ = ∑ y, (4 * H ^ 2) *
                      (d.prob x * d.prob y * (U x - U y) ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
                  _ = _ := by rw [Finset.mul_sum]
              _ = _ := by rw [Finset.mul_sum]
  unfold pairwiseVarianceExpression
  have hhalf := mul_le_mul_of_nonneg_left hdouble (by norm_num : 0 ≤ (1 / 2 : ℝ))
  nlinarith [hhalf]

end StatisticalRL.FiniteDistribution
