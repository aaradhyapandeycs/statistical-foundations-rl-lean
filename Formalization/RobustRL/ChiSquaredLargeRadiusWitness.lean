import Formalization.RobustRL.ChiSquaredClippedMoments
import Formalization.RobustRL.ChiSquaredPrimalDualWeakBridge

/-! χ² LargeRadiusWitness for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.ChiSquaredLargeRadiusWitness

open StatisticalRL.QLearning
open StatisticalRL.RobustRL.ChiSquaredDensity
open StatisticalRL.RobustRL.ChiSquaredClippedMoments
open StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge

variable {State : Type*} [Fintype State]

/-- Indicator of one value level. -/
noncomputable def levelIndicator (V : State → ℝ) (a : ℝ) (s : State) : ℝ :=
  if V s = a then 1 else 0

/-- Nominal mass at a specified value level. -/
noncomputable def levelMass (p : FiniteDistribution State) (V : State → ℝ)
    (a : ℝ) : ℝ := p.expectation (levelIndicator V a)

/-- Conditional-on-level density, totalized to zero away from the level. -/
noncomputable def levelDensity (V : State → ℝ) (a r : ℝ) (s : State) : ℝ :=
  if V s = a then r⁻¹ else 0

/-- Finite expectations ignore function changes outside positive nominal
support. This is used to show the clipped value is constant even when a
zero-mass state has value below the level. -/
theorem expectation_eq_const_of_eq_on_support
    (p : FiniteDistribution State) (f : State → ℝ) (c : ℝ)
    (hf : ∀ s, 0 < p.prob s → f s = c) : p.expectation f = c := by
  classical
  unfold FiniteDistribution.expectation
  calc
    (∑ s, p.prob s * f s) = ∑ s, p.prob s * c := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hz : p.prob s = 0
      · simp [hz]
      · have hp : 0 < p.prob s := by
          by_contra hn
          have hle : p.prob s ≤ 0 := le_of_not_gt hn
          exact hz (le_antisymm hle (p.prob_nonneg s))
        rw [hf s hp]
    _ = c := by
      rw [← Finset.sum_mul, p.sum_prob]
      ring

/-- Positive mass at a level produces an actual state on that level in nominal
support, including for arbitrary finite carriers. -/
theorem exists_positive_mass_on_level
    (p : FiniteDistribution State) (V : State → ℝ) (a r : ℝ)
    (hr : 0 < r) (hrmass : levelMass p V a = r) :
    ∃ s, 0 < p.prob s ∧ V s = a := by
  classical
  have hsum : 0 < ∑ s, p.prob s * levelIndicator V a s := by
    have hmasspos : 0 < levelMass p V a := by rw [hrmass]; exact hr
    simpa [levelMass, FiniteDistribution.expectation] using hmasspos
  obtain ⟨s, hs, hterm⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun s hs ↦ mul_nonneg (p.prob_nonneg s) (by
        unfold levelIndicator
        split_ifs <;> norm_num))).mp hsum
  have hp : 0 < p.prob s := by
    by_contra hn
    have hz : p.prob s = 0 :=
      le_antisymm (le_of_not_gt hn) (p.prob_nonneg s)
    simp [hz] at hterm
  have hi : 0 < levelIndicator V a s := by
    by_contra hn
    have hz : levelIndicator V a s = 0 :=
      le_antisymm (le_of_not_gt hn) (by
        unfold levelIndicator
        split_ifs <;> norm_num)
    rw [hz] at hterm
    simp at hterm
  have heq : V s = a := by
    by_contra h
    unfold levelIndicator at hi
    simp [h] at hi
  exact ⟨s, hp, heq⟩

/-- The level-density is nonnegative for a positive level mass. -/
theorem levelDensity_nonneg
    (V : State → ℝ) (a r : ℝ) (hr : 0 < r) (s : State) :
    0 ≤ levelDensity V a r s := by
  unfold levelDensity
  split_ifs
  · exact inv_nonneg.mpr hr.le
  · exact le_rfl

/-- Conditionalizing nominal mass on the level normalizes the density. -/
theorem levelDensity_mean_one
    (p : FiniteDistribution State) (V : State → ℝ) (a r : ℝ)
    (hr : 0 < r) (hrmass : levelMass p V a = r) :
    p.expectation (levelDensity V a r) = 1 := by
  have hfun : levelDensity V a r = fun s ↦ r⁻¹ * levelIndicator V a s := by
    funext s
    unfold levelDensity levelIndicator
    split_ifs <;> simp
  rw [hfun, p.expectation_mul]
  change r⁻¹ * levelMass p V a = 1
  rw [hrmass]
  field_simp [ne_of_gt hr]

/-- Exact χ² cost of conditioning on a positive-mass value level. -/
theorem levelDensity_chiSquared
    (p : FiniteDistribution State) (V : State → ℝ) (a r : ℝ)
    (hr : 0 < r) (hrmass : levelMass p V a = r) :
    p.expectation (fun s ↦ (levelDensity V a r s - 1) ^ 2) = r⁻¹ - 1 := by
  have hfun : (fun s ↦ (levelDensity V a r s - 1) ^ 2) =
      fun s ↦ 1 + ((r⁻¹ - 1) ^ 2 - 1) * levelIndicator V a s := by
    funext s
    by_cases h : V s = a
    · simp [levelDensity, levelIndicator, h] <;> ring
    · simp [levelDensity, levelIndicator, h]
  rw [hfun, p.expectation_add, p.expectation_const, p.expectation_mul]
  change 1 + ((r⁻¹ - 1) ^ 2 - 1) * levelMass p V a = r⁻¹ - 1
  rw [hrmass]
  field_simp [ne_of_gt hr]
  ring

/-- The clipped value at the minimum positive-support level equals that level
on support; values at nominal zero atoms below it do not affect moments. -/
theorem clipped_level_mean_eq
    (p : FiniteDistribution State) (V : State → ℝ) (a : ℝ)
    (hlevel : ∀ s, 0 < p.prob s → a ≤ V s) :
    p.expectation (fun s ↦ min (V s) a) = a := by
  rw [clipped_expectation]
  have hpositive : ∀ s, 0 < p.prob s → positivePart V a s = 0 := by
    intro s hs
    unfold positivePart
    rw [max_eq_right (sub_nonpos.mpr (hlevel s hs))]
  have hmean := expectation_eq_const_of_eq_on_support p (positivePart V a) 0 hpositive
  rw [hmean]
  ring

/-- At that level the clipped nominal variance is zero, including zero-mass
coordinates whose value may lie below `a`. -/
theorem clipped_level_variance_eq_zero
    (p : FiniteDistribution State) (V : State → ℝ) (a : ℝ)
    (hlevel : ∀ s, 0 < p.prob s → a ≤ V s) :
    p.variance (fun s ↦ min (V s) a) = 0 := by
  rw [clipped_variance]
  have hpositive : ∀ s, 0 < p.prob s → positivePart V a s = 0 := by
    intro s hs
    unfold positivePart
    rw [max_eq_right (sub_nonpos.mpr (hlevel s hs))]
  have hmean := expectation_eq_const_of_eq_on_support p (positivePart V a) 0 hpositive
  have hsquare := expectation_eq_const_of_eq_on_support p
    (fun s ↦ (positivePart V a s) ^ 2) 0 (by
      intro s hs
      change (positivePart V a s) ^ 2 = 0
      rw [hpositive s hs]
      norm_num)
  rw [hsquare, hmean]
  norm_num

/-- Large-radius endpoint: the actual conditional row, its exact Pearson cost,
its expected value, and the clipped scalar all agree at `a`. Positive mass at
the level also puts `a` in the interval of global carrier values used by the
source dual objective. -/
theorem large_radius_level_witness
    (p : FiniteDistribution State) (V : State → ℝ) (σ a r : ℝ)
    (hσ : 0 < σ) (hr : 0 < r)
    (hrmass : levelMass p V a = r)
    (hlevel : ∀ s, 0 < p.prob s → a ≤ V s)
    (hradius : r⁻¹ - 1 ≤ σ) :
    ∃ q : FiniteDistribution State,
      q ∈ qChiBall p σ ∧
      qChiSquared p q = r⁻¹ - 1 ∧
      q.expectation V = a ∧
      a ∈ Set.Icc (valueMin p V) (valueMax p V) ∧
      dualObjective p V σ a = a ∧
      dualObjective p V σ a ∈ dualValues p V σ := by
  classical
  let w := levelDensity V a r
  have hw : ∀ s, 0 ≤ w s := fun s ↦ levelDensity_nonneg V a r hr s
  have hnorm : p.expectation w = 1 := levelDensity_mean_one p V a r hr hrmass
  let q := densityRow p w hw hnorm
  have hcost : p.expectation (fun s ↦ (w s - 1) ^ 2) = r⁻¹ - 1 :=
    levelDensity_chiSquared p V a r hr hrmass
  have hqball : q ∈ qChiBall p σ := by
    exact densityRow_mem_ball p w hw hnorm σ (by rw [hcost]; exact hradius)
  have hqcost : qChiSquared p q = r⁻¹ - 1 := by
    rw [densityRow_chiSquared]
    exact hcost
  have hpayfun : (fun s ↦ w s * V s) = fun s ↦ a * w s := by
    funext s
    by_cases h : V s = a
    · simp [w, levelDensity, h] <;> ring
    · simp [w, levelDensity, h]
  have hpay : q.expectation V = a := by
    rw [densityRow_expectation p w V hw hnorm, hpayfun, p.expectation_mul, hnorm]
    ring
  have hclipmean := clipped_level_mean_eq p V a hlevel
  have hclipvar := clipped_level_variance_eq_zero p V a hlevel
  have hdual : dualObjective p V σ a = a := by
    simp [dualObjective, hclipmean, hclipvar]
  obtain ⟨s, hspos, hsa⟩ := exists_positive_mass_on_level p V a r hr hrmass
  have hinterval : a ∈ Set.Icc (valueMin p V) (valueMax p V) := by
    constructor
    · simpa [hsa] using valueMin_le p V s
    · simpa [hsa] using le_valueMax p V s
  refine ⟨q, hqball, hqcost, hpay, hinterval, hdual, ?_⟩
  exact ⟨a, hinterval, rfl⟩

end StatisticalRL.RobustRL.ChiSquaredLargeRadiusWitness
