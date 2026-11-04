import Formalization.RobustRL.ChiSquaredClippedMoments
import Formalization.RobustRL.ChiSquaredPrimalDualWeakBridge

/-! χ² PositiveRootWitness for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/

namespace StatisticalRL.RobustRL.ChiSquaredPositiveRootWitness

open StatisticalRL.RobustRL.ChiSquaredDensity
open StatisticalRL.RobustRL.ChiSquaredClippedMoments

variable {State : Type*} [Fintype State]

/-- A positive clipped-moment root constructs a supported χ²-feasible row
with exact cost and expectation equal to the source clipped scalar. No
threshold-existence or primal/dual optimality conclusion is assumed. -/
theorem positive_root_feasible_witness
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (α σ : ℝ)
    (hσ : 0 ≤ σ)
    (hm : 0 < p.expectation (positivePart V α))
    (hroot : p.expectation (fun s ↦ (positivePart V α s) ^ 2) =
      (1 + σ) * (p.expectation (positivePart V α)) ^ 2) :
    ∃ q : StatisticalRL.FiniteDistribution State,
      q ∈ StatisticalRL.QLearning.qChiBall p σ ∧
      StatisticalRL.QLearning.qChiSquared p q = σ ∧
      q.expectation V =
        StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective p V σ α := by
  classical
  let z : State → ℝ := positivePart V α
  let m : ℝ := p.expectation z
  let w : State → ℝ := fun s ↦ m⁻¹ * z s
  have hm' : 0 < m := hm
  have hmne : m ≠ 0 := ne_of_gt hm'
  have hroot' : p.expectation (fun s ↦ z s ^ 2) = (1 + σ) * m ^ 2 := hroot
  have hw : ∀ s, 0 ≤ w s := by
    intro s
    exact mul_nonneg (inv_nonneg.mpr hm'.le) (positivePart_nonneg V α s)
  have hnorm : p.expectation w = 1 := by
    change p.expectation (fun s ↦ m⁻¹ * z s) = 1
    rw [p.expectation_mul]
    exact inv_mul_cancel₀ hmne
  have hcost : p.expectation (fun s ↦ (w s - 1) ^ 2) = σ := by
    have hpoint : (fun s ↦ (w s - 1) ^ 2) =
        fun s ↦ (m⁻¹)^2 * z s ^ 2 - (2 * m⁻¹) * z s + 1 := by
      funext s
      dsimp [w]
      ring
    rw [hpoint, p.expectation_add, p.expectation_sub, p.expectation_mul,
      p.expectation_mul, p.expectation_const, hroot']
    change m⁻¹ ^ 2 * ((1 + σ) * m ^ 2) - (2 * m⁻¹) * m + 1 = σ
    field_simp [hmne]
    <;> ring
  let q := densityRow p w hw hnorm
  have hball : q ∈ StatisticalRL.QLearning.qChiBall p σ := by
    exact densityRow_mem_ball p w hw hnorm σ hcost.le
  have hcostq : StatisticalRL.QLearning.qChiSquared p q = σ := by
    rw [densityRow_chiSquared]
    exact hcost
  have hpayoff : q.expectation V = α - (1 + σ) * m := by
    rw [densityRow_expectation]
    have hpoint : (fun s ↦ w s * V s) = fun s ↦ m⁻¹ * (z s * V s) := by
      funext s
      dsimp [w]
      ring
    rw [hpoint, p.expectation_mul]
    have hmoment : p.expectation (fun s ↦ z s * V s) =
        α * m - p.expectation (fun s ↦ z s ^ 2) :=
      weighted_positivePart_value p V α
    rw [hmoment, hroot']
    field_simp [hmne]
    <;> ring
  have hvariance : p.variance (fun s ↦ min (V s) α) = σ * m ^ 2 := by
    rw [clipped_variance]
    change p.expectation (fun s ↦ z s ^ 2) - m ^ 2 = σ * m ^ 2
    rw [hroot']
    ring
  have hsqrt : Real.sqrt (σ * p.variance (fun s ↦ min (V s) α)) = σ * m := by
    rw [hvariance]
    have hsq : σ * (σ * m ^ 2) = (σ * m) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hσ hm'.le)]
  have hscalar : StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective
      p V σ α = α - (1 + σ) * m := by
    unfold StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective
    rw [clipped_expectation, hsqrt]
    change α - m - σ * m = α - (1 + σ) * m
    ring
  exact ⟨q, hball, hcostq, hpayoff.trans hscalar.symm⟩
end StatisticalRL.RobustRL.ChiSquaredPositiveRootWitness
