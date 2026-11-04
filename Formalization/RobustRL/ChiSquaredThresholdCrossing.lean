import Formalization.RobustRL.ChiSquaredClippedMoments
import Formalization.RobustRL.ChiSquaredLargeRadiusWitness
import Mathlib.Topology.Order.IntermediateValue

/-! χ² ThresholdCrossing for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.ChiSquaredThresholdCrossing

open StatisticalRL.QLearning
open StatisticalRL.RobustRL.ChiSquaredDensity
open StatisticalRL.RobustRL.ChiSquaredClippedMoments
open StatisticalRL.RobustRL.ChiSquaredLargeRadiusWitness
open StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge

variable {State : Type*} [Fintype State]

/-- Residual whose zero is the clipped-moment equation in the source χ²
construction. -/
noncomputable def clippedMomentResidual (p : FiniteDistribution State)
    (V : State → ℝ) (σ α : ℝ) : ℝ :=
  p.expectation (fun s ↦ (positivePart V α s) ^ 2) -
    (1 + σ) * (p.expectation (positivePart V α)) ^ 2

/-- Finite expectations are unchanged when two functions agree on positive
nominal support. This explicitly preserves arbitrary zero-mass coordinates. -/
theorem expectation_eq_on_support
    (p : FiniteDistribution State) (f g : State → ℝ)
    (hfg : ∀ s, 0 < p.prob s → f s = g s) :
    p.expectation f = p.expectation g := by
  classical
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hz : p.prob s = 0
  · simp [hz]
  · have hp : 0 < p.prob s := by
      by_contra hn
      have hle : p.prob s ≤ 0 := le_of_not_gt hn
      exact hz (le_antisymm hle (p.prob_nonneg s))
    rw [hfg s hp]

/-- At the global value upper bound, the clipped residual is exactly the
failure of the source small-radius condition. -/
theorem clippedMomentResidual_at_upper_eq
    (p : FiniteDistribution State) (V : State → ℝ) (σ b : ℝ)
    (hVupper : ∀ s, V s ≤ b) :
    clippedMomentResidual p V σ b =
      p.variance V - σ * (b - p.expectation V) ^ 2 := by
  have hclip : (fun s ↦ min (V s) b) = V := by
    funext s
    exact min_eq_left (hVupper s)
  have hmean := clipped_expectation p V b
  rw [hclip] at hmean
  have hm : p.expectation (positivePart V b) = b - p.expectation V := by
    linarith
  have hvariance := clipped_variance p V b
  rw [hclip] at hvariance
  have hsecond : p.expectation (fun s ↦ (positivePart V b s) ^ 2) =
      p.variance V + (b - p.expectation V) ^ 2 := by
    rw [hm] at hvariance
    linarith
  unfold clippedMomentResidual
  rw [hm, hsecond]
  ring

/-- The strict small-radius condition implies a positive midpoint residual. -/
theorem clippedMomentResidual_midpoint_pos
    (p : FiniteDistribution State) (V : State → ℝ) (σ a c r : ℝ)
    (hσ : 0 ≤ σ) (hr : 0 < r) (hrmass : levelMass p V a = r)
    (hac : a < c)
    (hgap : ∀ s, 0 < p.prob s → V s = a ∨ c ≤ V s)
    (hsmall : σ < r⁻¹ - 1) :
    0 < clippedMomentResidual p V σ ((a + c) / 2) := by
  let α₀ : ℝ := (a + c) / 2
  let d : ℝ := (c - a) / 2
  have ha0 : a < α₀ := by dsimp [α₀]; linarith
  have h0c : α₀ < c := by dsimp [α₀]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hfactor : 0 < 1 - (1 + σ) * r := by
    have hmul : 1 + σ < r⁻¹ := by linarith
    have hmul' := mul_lt_mul_of_pos_right hmul hr
    have hcancel : r⁻¹ * r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    rw [hcancel] at hmul'
    exact sub_pos.mpr hmul'
  have hpoint : ∀ s, 0 < p.prob s →
      positivePart V α₀ s = d * levelIndicator V a s := by
    intro s hs
    rcases hgap s hs with hsa | hsc
    · have hα : 0 ≤ α₀ - V s := by rw [hsa]; linarith
      have hI : levelIndicator V a s = 1 := by simp [levelIndicator, hsa]
      have hZ : positivePart V α₀ s = α₀ - a := by
        unfold positivePart
        rw [hsa, max_eq_left (by linarith [ha0])]
      rw [hI, hZ]
      dsimp [d, α₀]
      ring
    · have hne : V s ≠ a := by
        intro heq
        rw [heq] at hsc
        linarith
      have hα : α₀ ≤ V s := le_trans h0c.le hsc
      have hI : levelIndicator V a s = 0 := by simp [levelIndicator, hne]
      have hZ : positivePart V α₀ s = 0 := by
        unfold positivePart
        exact max_eq_right (sub_nonpos.mpr hα)
      rw [hI, hZ]
      ring
  have hpointSq : ∀ s, 0 < p.prob s →
      (positivePart V α₀ s) ^ 2 = d ^ 2 * levelIndicator V a s := by
    intro s hs
    rw [hpoint s hs]
    by_cases hsa : V s = a
    · simp [levelIndicator, hsa]
    · simp [levelIndicator, hsa]
  have hmean : p.expectation (positivePart V α₀) = r * d := by
    calc
      p.expectation (positivePart V α₀) =
          p.expectation (fun s ↦ d * levelIndicator V a s) :=
        expectation_eq_on_support p _ _ hpoint
      _ = d * p.expectation (levelIndicator V a) := p.expectation_mul d _
      _ = d * r := by change d * levelMass p V a = d * r; rw [hrmass]
      _ = r * d := by ring
  have hsecond : p.expectation (fun s ↦ (positivePart V α₀ s) ^ 2) = r * d ^ 2 := by
    calc
      p.expectation (fun s ↦ (positivePart V α₀ s) ^ 2) =
          p.expectation (fun s ↦ d ^ 2 * levelIndicator V a s) :=
        expectation_eq_on_support p _ _ hpointSq
      _ = d ^ 2 * p.expectation (levelIndicator V a) := p.expectation_mul (d ^ 2) _
      _ = d ^ 2 * r := by change d ^ 2 * levelMass p V a = d ^ 2 * r; rw [hrmass]
      _ = r * d ^ 2 := by ring
  have hformula : clippedMomentResidual p V σ α₀ =
      r * d ^ 2 * (1 - (1 + σ) * r) := by
    unfold clippedMomentResidual
    rw [hmean, hsecond]
    ring
  rw [hformula]
  positivity

/-- Continuity of the finite clipped first and second moments. -/
theorem clippedMomentResidual_continuous
    (p : FiniteDistribution State) (V : State → ℝ) (σ : ℝ) :
    Continuous (clippedMomentResidual p V σ) := by
  have hz (s : State) : Continuous (fun α : ℝ ↦ positivePart V α s) := by
    unfold positivePart
    exact continuous_max.comp
      ((continuous_id.sub continuous_const).prodMk continuous_const)
  have hm : Continuous (fun α : ℝ ↦ p.expectation (positivePart V α)) := by
    unfold FiniteDistribution.expectation
    exact continuous_finset_sum _ (fun s _ ↦ continuous_const.mul (hz s))
  have hsquare : Continuous (fun α : ℝ ↦
      p.expectation (fun s ↦ (positivePart V α s) ^ 2)) := by
    unfold FiniteDistribution.expectation
    exact continuous_finset_sum _ (fun s _ ↦ continuous_const.mul ((hz s).pow 2))
  unfold clippedMomentResidual
  exact hsquare.sub (continuous_const.mul (hm.pow 2))

/-- Crossing theorem for the interior positive-support branch. The level gap,
positive mass, and failed endpoint inequality are branch conditions that a
source-facing caller must derive; they are not asserted for arbitrary inputs. -/
theorem clippedMoment_root_exists
    (p : FiniteDistribution State) (V : State → ℝ) (σ a c r b : ℝ)
    (hσ : 0 ≤ σ) (hr : 0 < r) (hrmass : levelMass p V a = r)
    (hac : a < c)
    (hgap : ∀ s, 0 < p.prob s → V s = a ∨ c ≤ V s)
    (hcB : c ≤ b) (hb : b = valueMax p V)
    (hsmall : σ < r⁻¹ - 1)
    (hfail : p.variance V < σ * (b - p.expectation V) ^ 2) :
    ∃ α, (a + c) / 2 < α ∧ α < b ∧
      α ∈ Set.Icc (valueMin p V) (valueMax p V) ∧
      0 < p.expectation (positivePart V α) ∧
      clippedMomentResidual p V σ α = 0 := by
  have hVupper : ∀ s, V s ≤ b := by
    intro s
    rw [hb]
    exact le_valueMax p V s
  have hFupper := clippedMomentResidual_at_upper_eq p V σ b hVupper
  have hFneg : clippedMomentResidual p V σ b < 0 := by
    rw [hFupper]
    linarith
  have hFmid := clippedMomentResidual_midpoint_pos p V σ a c r hσ hr hrmass hac hgap hsmall
  let α₀ : ℝ := (a + c) / 2
  have h0c : α₀ < c := by dsimp [α₀]; linarith
  have h0b : α₀ ≤ b := (h0c.le.trans hcB)
  have hcont := clippedMomentResidual_continuous p V σ
  have himage : 0 ∈ Set.Icc (clippedMomentResidual p V σ b)
      (clippedMomentResidual p V σ α₀) := ⟨hFneg.le, hFmid.le⟩
  have hroot_image : 0 ∈ clippedMomentResidual p V σ '' Set.Icc α₀ b :=
    (intermediate_value_Icc' h0b hcont.continuousOn) himage
  obtain ⟨α, hαIcc, hroot⟩ := hroot_image
  have hlow : α₀ < α := by
    have hne : α ≠ α₀ := by
      intro heq
      subst α
      linarith
    exact lt_of_le_of_ne hαIcc.1 hne.symm
  have hupp : α < b := by
    have hne : α ≠ b := by
      intro heq
      subst α
      linarith
    exact lt_of_le_of_ne hαIcc.2 hne
  have hpositive : 0 < p.expectation (positivePart V α) := by
    let d : ℝ := (c - a) / 2
    have hd : 0 < d := by dsimp [d]; linarith
    have haα : a < α := by dsimp [α₀] at hlow; linarith
    have hpoint : ∀ s, 0 < p.prob s →
        d * levelIndicator V a s ≤ positivePart V α s := by
      intro s hs
      rcases hgap s hs with hsa | hsc
      · have hI : levelIndicator V a s = 1 := by simp [levelIndicator, hsa]
        have hZ : positivePart V α s = α - a := by
          unfold positivePart
          rw [hsa, max_eq_left (by linarith : 0 ≤ α - a)]
        rw [hI, hZ]
        dsimp [d, α₀] at hlow ⊢
        linarith
      · have hne : V s ≠ a := by
          intro heq
          rw [heq] at hsc
          linarith [hac]
        have hI : levelIndicator V a s = 0 := by simp [levelIndicator, hne]
        rw [hI]
        simpa only [mul_zero] using positivePart_nonneg V α s
    have hfloor : p.expectation (fun s ↦ d * levelIndicator V a s) = d * r := by
      rw [p.expectation_mul]
      change d * levelMass p V a = d * r
      rw [hrmass]
    have hfloorpos : 0 < p.expectation (fun s ↦ d * levelIndicator V a s) := by
      rw [hfloor]
      positivity
    let lower : State → ℝ := fun s ↦
      if 0 < p.prob s then d * levelIndicator V a s else 0
    have heq : p.expectation (fun s ↦ d * levelIndicator V a s) =
        p.expectation lower := by
      apply expectation_eq_on_support
      intro s hs
      simp [lower, hs]
    have hmono : p.expectation lower ≤ p.expectation (positivePart V α) :=
      p.expectation_mono (fun s ↦ by
        by_cases hs : 0 < p.prob s
        · simp [lower, hs]
          exact hpoint s hs
        · simp [lower, hs]
          exact positivePart_nonneg V α s)
    rw [heq] at hfloorpos
    exact lt_of_lt_of_le hfloorpos hmono
  have hinterval : α ∈ Set.Icc (valueMin p V) (valueMax p V) := by
    obtain ⟨s, hs, hsa⟩ := exists_positive_mass_on_level p V a r hr hrmass
    constructor
    · have haMin : valueMin p V ≤ a := by simpa [hsa] using valueMin_le p V s
      dsimp [α₀] at hlow
      linarith
    · simpa [hb] using hupp.le
  exact ⟨α, by simpa [α₀] using hlow, hupp, hinterval, hpositive, hroot⟩

end StatisticalRL.RobustRL.ChiSquaredThresholdCrossing
