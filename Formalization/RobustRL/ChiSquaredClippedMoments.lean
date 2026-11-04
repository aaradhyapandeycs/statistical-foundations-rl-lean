import Formalization.RobustRL.ChiSquaredDensity

/-! χ² ClippedMoments for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/

namespace StatisticalRL.RobustRL.ChiSquaredClippedMoments

variable {State : Type*} [Fintype State]

/-- The amount by which a value falls below a threshold. -/
def positivePart (V : State → ℝ) (α : ℝ) (s : State) : ℝ :=
  max (α - V s) 0

theorem positivePart_nonneg (V : State → ℝ) (α : ℝ) (s : State) :
    0 ≤ positivePart V α s := le_max_right _ _

theorem clip_eq_sub_positivePart (V : State → ℝ) (α : ℝ) (s : State) :
    min (V s) α = α - positivePart V α s := by
  by_cases h : V s ≤ α
  · rw [min_eq_left h, positivePart, max_eq_left (sub_nonneg.mpr h)]
    ring
  · have hα : α ≤ V s := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hα, positivePart, max_eq_right (sub_nonpos.mpr hα)]
    ring

theorem positivePart_mul_value (V : State → ℝ) (α : ℝ) (s : State) :
    positivePart V α s * V s =
      α * positivePart V α s - (positivePart V α s) ^ 2 := by
  by_cases h : V s ≤ α
  · simp only [positivePart, max_eq_left (sub_nonneg.mpr h)]
    ring
  · have hα : α ≤ V s := le_of_lt (lt_of_not_ge h)
    simp only [positivePart, max_eq_right (sub_nonpos.mpr hα)]
    ring

theorem clipped_expectation (p : FiniteDistribution State) (V : State → ℝ) (α : ℝ) :
    p.expectation (fun s ↦ min (V s) α) = α - p.expectation (positivePart V α) := by
  have he : (fun s ↦ min (V s) α) = fun s ↦ α - positivePart V α s := by
    funext s
    exact clip_eq_sub_positivePart V α s
  rw [he, p.expectation_sub, p.expectation_const]

theorem clipped_variance (p : FiniteDistribution State) (V : State → ℝ) (α : ℝ) :
    p.variance (fun s ↦ min (V s) α) =
      p.expectation (fun s ↦ (positivePart V α s) ^ 2) -
        (p.expectation (positivePart V α)) ^ 2 := by
  have he : (fun s ↦ (min (V s) α) ^ 2) =
      fun s ↦ α ^ 2 - (2 * α) * positivePart V α s +
        (positivePart V α s) ^ 2 := by
    funext s
    rw [clip_eq_sub_positivePart]
    ring
  unfold FiniteDistribution.variance
  rw [clipped_expectation, he, p.expectation_add, p.expectation_sub,
    p.expectation_const, p.expectation_mul]
  ring

theorem weighted_positivePart_value (p : FiniteDistribution State)
    (V : State → ℝ) (α : ℝ) :
    p.expectation (fun s ↦ positivePart V α s * V s) =
      α * p.expectation (positivePart V α) -
        p.expectation (fun s ↦ (positivePart V α s) ^ 2) := by
  have he : (fun s ↦ positivePart V α s * V s) =
      fun s ↦ α * positivePart V α s - (positivePart V α s) ^ 2 := by
    funext s
    exact positivePart_mul_value V α s
  rw [he, p.expectation_sub, p.expectation_mul]

end StatisticalRL.RobustRL.ChiSquaredClippedMoments
