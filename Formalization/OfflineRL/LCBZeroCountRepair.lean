import Formalization.OfflineRL.SampledArmsConfidence
import Formalization.OfflineRL.BanditDefinitions

/-! LCB with the commented zero-count fallback.

Source: Algorithm `alg:MAB-LCB`, `chapters/offlineRL.tex:400–443`, theorem
`:456–471`, proof `:524–578`. The active formula divides by the count and is
undefined at zero; the commented line `:429–430` sets mean 0 and radius 1.
This module formalizes that separately identified fallback and its deterministic
selection implication. The two zero-count conventions are not interchangeable;
see `docs/SOURCE-ISSUES.md#C18`.
-/

namespace StatisticalRL.OfflineRL

variable {Arm : Type*} [Fintype Arm] [DecidableEq Arm]

theorem lcbFallback_le {N : ℕ} (r : Arm → ℝ) (hr0 : ∀ b, 0 ≤ r b)
    (a : Fin N → Arm) (z : Fin N → ℝ) (δ : ℝ)
    (hconf : ∀ b, 0 < armCount a b →
      |empiricalArmMean r a z b - r b| ≤ armRadius (Fintype.card Arm) δ (armCount a b))
    (b : Arm) : lcbFallback r a z δ b ≤ r b := by
  unfold lcbFallback
  split_ifs with h
  · linarith [hr0 b]
  · have := hconf b (Nat.pos_of_ne_zero h)
    rw [abs_le] at this
    linarith [this.2]

/-- Deterministic selection implication under the commented fallback. -/
theorem lcbFallback_regret {N : ℕ} (r : Arm → ℝ) (hr0 : ∀ b, 0 ≤ r b)
    (a : Fin N → Arm) (z : Fin N → ℝ) (δ : ℝ)
    (hconf : ∀ b, 0 < armCount a b →
      |empiricalArmMean r a z b - r b| ≤ armRadius (Fintype.card Arm) δ (armCount a b))
    (aStar : Arm) (hpos : 0 < armCount a aStar)
    (aL : Arm) (hsel : ∀ b, lcbFallback r a z δ b ≤ lcbFallback r a z δ aL) :
    r aStar - r aL ≤ 2 * armRadius (Fintype.card Arm) δ (armCount a aStar) := by
  have hS := hconf aStar hpos
  rw [abs_le] at hS
  have hsel' := hsel aStar
  have hL := lcbFallback_le r hr0 a z δ hconf aL
  have hval : lcbFallback r a z δ aStar =
      empiricalArmMean r a z aStar - armRadius (Fintype.card Arm) δ (armCount a aStar) := by
    unfold lcbFallback
    rw [if_neg (by omega)]
  linarith [hS.1]

end StatisticalRL.OfflineRL
