import Formalization.OfflineRL.SampledArmsConfidence
import Formalization.OfflineRL.BanditDefinitions

/-! Confidence bridge for the zero-count-safe LCB convention.

Source: Algorithm `alg:MAB-LCB`, `chapters/offlineRL.tex:400–443`, theorem
`:456–471`, proof `:524–578`. At zero count the commented fallback sets mean 0
and radius 1; at positive counts the printed formula is used. This is not the
active undefined zero-count pseudocode; see `docs/SOURCE-ISSUES.md#C18`.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL

variable {Arm : Type*} [Fintype Arm] [DecidableEq Arm]

/-- Deterministic sandwich on the sampled-arm confidence event. -/
theorem safe_sandwich_of_confidence {N : ℕ} (r : Arm → ℝ) (hr0 : ∀ b, 0 ≤ r b)
    (hr1 : ∀ b, r b ≤ 1) (a : Fin N → Arm) (z : Fin N → ℝ) (δ : ℝ)
    (hconf : ∀ b, 0 < armCount a b →
      |empiricalArmMean r a z b - r b| ≤ armRadius (Fintype.card Arm) δ (armCount a b))
    (b : Arm) :
    safeMean r a z b - safeRadius a δ b ≤ r b ∧ r b ≤ safeMean r a z b + safeRadius a δ b := by
  unfold safeMean safeRadius
  split_ifs with h
  · constructor <;> linarith [hr0 b, hr1 b]
  · have := hconf b (Nat.pos_of_ne_zero h)
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]

/-- Actual-law confidence bridge: with probability at least `1 − δ/2`,
`LCB_b ≤ r(b) ≤ UCB_b` holds simultaneously for every arm. -/
theorem safe_lcb_confidence [MeasurableSpace Arm] [MeasurableSingletonClass Arm]
    (d : Measure Arm) [IsProbabilityMeasure d] (r : Arm → ℝ) (hr0 : ∀ b, 0 ≤ r b)
    (hr1 : ∀ b, r b ≤ 1) (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 ≤
      ((Measure.pi fun _ : Fin N => d).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)).real
        {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ b,
          safeMean r ω.1 ω.2 b - safeRadius ω.1 δ b ≤ r b ∧
            r b ≤ safeMean r ω.1 ω.2 b + safeRadius ω.1 δ b} := by
  have h := allSampledArms_confidence d r N δ hδ hδ1
  refine h.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro ω hω b
  exact safe_sandwich_of_confidence r hr0 hr1 ω.1 ω.2 δ hω b

end StatisticalRL.OfflineRL
