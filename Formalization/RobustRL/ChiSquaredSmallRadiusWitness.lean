import Formalization.RobustRL.ChiSquaredDensity
import Formalization.RobustRL.ChiSquaredPrimalDualWeakBridge

/-! χ² SmallRadiusWitness for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/
namespace StatisticalRL.RobustRL.ChiSquaredSmallRadiusWitness
open StatisticalRL.RobustRL.ChiSquaredDensity
variable {State : Type*} [Fintype State]

theorem small_radius_feasible_witness
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (b σ : ℝ)
    (hσ : 0 ≤ σ) (hv : 0 < p.variance V) (hb : ∀ s, V s ≤ b)
    (hsmall : σ * (b - p.expectation V)^2 ≤ p.variance V) :
    ∃ q : StatisticalRL.FiniteDistribution State,
      q ∈ StatisticalRL.QLearning.qChiBall p σ ∧
      StatisticalRL.QLearning.qChiSquared p q = σ ∧
      q.expectation V = p.expectation V - Real.sqrt (σ * p.variance V) ∧
      q.expectation V =
        StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective p V σ b := by
  classical
  let μ := p.expectation V
  let r := Real.sqrt (p.variance V)
  let c := Real.sqrt σ / r
  let w : State → ℝ := fun s ↦ 1 - c * (V s - μ)
  have hr : 0 < r := Real.sqrt_pos.mpr hv
  have hrne : r ≠ 0 := ne_of_gt hr
  have hrsq : r ^ 2 = p.variance V := Real.sq_sqrt hv.le
  have hssq : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) hr.le
  have hm : 0 ≤ b - μ := sub_nonneg.mpr (p.expectation_le_const hb)
  have hsqrt : Real.sqrt σ * (b - μ) ≤ r := by
    have h := Real.sqrt_le_sqrt hsmall
    rw [Real.sqrt_mul hσ, Real.sqrt_sq_eq_abs, abs_of_nonneg hm] at h
    exact h
  have hcsmall : c * (b - μ) ≤ 1 := by
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hr).2
    simpa using hsqrt
  have hw : ∀ s, 0 ≤ w s := by
    intro s
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_right (hb s) μ) hc
    dsimp [w]
    linarith
  have hzero : p.expectation (fun s ↦ V s - μ) = 0 := by
    rw [p.expectation_sub, p.expectation_const]
    simp [μ]
  have hnorm : p.expectation w = 1 := by
    change p.expectation (fun s ↦ 1 - c * (V s - μ)) = 1
    rw [p.expectation_sub, p.expectation_const, p.expectation_mul, hzero]
    ring
  have hcost : p.expectation (fun s ↦ (w s - 1)^2) = σ := by
    have he : (fun s ↦ (w s - 1)^2) = fun s ↦ c^2 * (V s - μ)^2 := by
      funext s
      dsimp [w]
      ring
    rw [he, p.expectation_mul, ← p.variance_eq_expectation_centered_sq]
    change c^2 * p.variance V = σ
    rw [← hrsq]
    dsimp [c]
    field_simp
    exact hssq
  let q := densityRow p w hw hnorm
  have hball : q ∈ StatisticalRL.QLearning.qChiBall p σ :=
    densityRow_mem_ball p w hw hnorm σ hcost.le
  have hcostq : StatisticalRL.QLearning.qChiSquared p q = σ := by
    rw [densityRow_chiSquared]
    exact hcost
  have hgain : c * p.variance V = Real.sqrt (σ * p.variance V) := by
    rw [Real.sqrt_mul hσ]
    change c * p.variance V = Real.sqrt σ * r
    rw [← hrsq]
    dsimp [c]
    field_simp
  have hpayoff : q.expectation V = μ - c * p.variance V := by
    rw [densityRow_expectation]
    have he : (fun s ↦ w s * V s) =
        fun s ↦ V s - c * (V s^2) + (c * μ) * V s := by
      funext s
      dsimp [w]
      ring
    rw [he, p.expectation_add, p.expectation_sub, p.expectation_mul,
      p.expectation_mul]
    unfold StatisticalRL.FiniteDistribution.variance
    change μ - c * p.expectation (fun s ↦ V s ^ 2) + c * μ * μ = _
    ring
  have hclip : (fun s ↦ min (V s) b) = V := by
    funext s
    exact min_eq_left (hb s)
  have hscalar : StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective
      p V σ b = μ - Real.sqrt (σ * p.variance V) := by
    unfold StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective
    rw [hclip]
  exact ⟨q, hball, hcostq, by rw [hpayoff, hgain], by rw [hpayoff, hgain, hscalar]⟩
end StatisticalRL.RobustRL.ChiSquaredSmallRadiusWitness
