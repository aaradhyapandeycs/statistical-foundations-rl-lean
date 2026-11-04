import Formalization.RobustRL.ChiSquaredThresholdCrossing
import Formalization.RobustRL.ChiSquaredPositiveRootWitness
import Formalization.RobustRL.ChiSquaredSmallRadiusWitness
import Formalization.RobustRL.ChiSquaredSupportedLevels
import Formalization.RobustRL.ChiSquaredZeroVarianceWitness

/-! χ² SourceMaximum for finite probability rows. This module supports the χ² branch of Lemma 7.1, robust_RL.tex:302–324. -/
namespace StatisticalRL.RobustRL.ChiSquaredSourceMaximum
open StatisticalRL
open StatisticalRL.QLearning
open StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge
open StatisticalRL.RobustRL.ChiSquaredLargeRadiusWitness
open StatisticalRL.RobustRL.ChiSquaredClippedMoments
open StatisticalRL.RobustRL.ChiSquaredThresholdCrossing
open StatisticalRL.RobustRL.ChiSquaredSupportedLevels
open StatisticalRL.RobustRL.ChiSquaredPositiveRootWitness
open StatisticalRL.RobustRL.ChiSquaredSmallRadiusWitness
open StatisticalRL.RobustRL.ChiSquaredZeroVarianceWitness
variable {State : Type*} [Fintype State]

/-- A feasible row and a threshold in the actual global value interval match;
the source infimum is the attained scalar maximum over that interval. -/
theorem chiSquared_source_maximum
    (p : FiniteDistribution State) (V : State → ℝ) (σ : ℝ)
    (hσ : 0 < σ) (hV : ∀ s, 0 ≤ V s) :
    ∃ (q : FiniteDistribution State) (α : ℝ),
      q ∈ qChiBall p σ ∧ α ∈ Set.Icc (valueMin p V) (valueMax p V) ∧
      q.expectation V = dualObjective p V σ α ∧
      sInf (qRobustExpectations p σ V) = dualObjective p V σ α ∧
      ∀ β ∈ Set.Icc (valueMin p V) (valueMax p V),
        dualObjective p V σ β ≤ dualObjective p V σ α := by
  classical
  let b := valueMax p V
  have hb : ∀ s, V s ≤ b := le_valueMax p V
  have hbI : b ∈ Set.Icc (valueMin p V) (valueMax p V) :=
    ⟨valueMin_le_valueMax p V, le_rfl⟩
  obtain ⟨a, s₀, hp₀, hs₀, hmin, hrpos, hrle, hnext⟩ :=
    exists_supported_minimum_and_next p V b hb
  let r := p.expectation (fun s ↦ if V s = a then 1 else 0)
  have hr : 0 < r := hrpos
  have hrmass : levelMass p V a = r := by rfl
  have hwitness : ∃ (q : FiniteDistribution State) (α : ℝ),
      q ∈ qChiBall p σ ∧ α ∈ Set.Icc (valueMin p V) (valueMax p V) ∧
      q.expectation V = dualObjective p V σ α := by
    by_cases hlarge : r⁻¹ - 1 ≤ σ
    · obtain ⟨q, hq, _, hpay, hinterval, hdual, _⟩ :=
        large_radius_level_witness p V σ a r hσ hr hrmass hmin hlarge
      exact ⟨q, a, hq, hinterval, hpay.trans hdual.symm⟩
    · have hsmall : σ < r⁻¹ - 1 := lt_of_not_ge hlarge
      by_cases hv : p.variance V = 0
      · obtain ⟨hq, hdual⟩ := nominal_zero_variance_witness p V σ b hσ.le hv hb
        exact ⟨p, b, hq, hbI, hdual.symm⟩
      · have hvpos : 0 < p.variance V := lt_of_le_of_ne (p.variance_nonneg V) (Ne.symm hv)
        by_cases hend : σ * (b - p.expectation V)^2 ≤ p.variance V
        · obtain ⟨q, hq, _, _, hdual⟩ :=
            small_radius_feasible_witness p V b σ hσ.le hvpos hb hend
          exact ⟨q, b, hq, hbI, hdual⟩
        · have hrlt : r < 1 := by
            have hh := mul_lt_mul_of_pos_right hsmall hr
            have hi : r⁻¹ * r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
            have hn := mul_nonneg hσ.le hr.le
            nlinarith
          obtain ⟨c, s₁, hp₁, hs₁, hac, hcb, hgap⟩ := hnext hrlt
          have hfail : p.variance V < σ * (b - p.expectation V)^2 := lt_of_not_ge hend
          obtain ⟨α, _, _, hα, hm, hroot⟩ :=
            clippedMoment_root_exists p V σ a c r b hσ.le hr hrmass hac hgap hcb rfl hsmall hfail
          have hroot' : p.expectation (fun s ↦ (positivePart V α s)^2) =
              (1 + σ) * (p.expectation (positivePart V α))^2 := by
            unfold clippedMomentResidual at hroot
            linarith
          obtain ⟨q, hq, _, hpay⟩ := positive_root_feasible_witness p V α σ hσ.le hm hroot'
          exact ⟨q, α, hq, hα, hpay⟩
  obtain ⟨q, α, hq, hα, hpay⟩ := hwitness
  have hweak : ∀ β, dualObjective p V σ β ≤ q.expectation V := by
    intro β
    exact StatisticalRL.RobustRL.ChiSquaredWeakDuality.clipped_scalar_le_feasible_expectation p q V σ β hq
  have hinf : sInf (qRobustExpectations p σ V) = dualObjective p V σ α := by
    apply le_antisymm
    · exact (csInf_le (primalValues_bddBelow p V σ) ⟨q, hq, rfl⟩).trans_eq hpay
    · apply le_csInf (primalValues_nonempty p V σ hσ)
      rintro z ⟨q', hq', rfl⟩
      exact StatisticalRL.RobustRL.ChiSquaredWeakDuality.clipped_scalar_le_feasible_expectation p q' V σ α hq'
  refine ⟨q, α, hq, hα, hpay, hinf, ?_⟩
  intro β hβ
  exact (hweak β).trans_eq hpay
end StatisticalRL.RobustRL.ChiSquaredSourceMaximum
