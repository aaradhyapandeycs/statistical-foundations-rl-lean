import Formalization.RobustRL.TVCore
import Mathlib

/-! Pointwise clipped weak-duality estimates for Chapter 7 robust TV.

The TV norm is the existing finite half-L1 API; the source event-TV bridge is
provided by `Formalization.RobustRL.TVCore`. This module proves only the weak
pointwise direction. -/

namespace StatisticalRL.RobustRL

variable {State : Type*} [Fintype State] [Nonempty State]

/-- Expectation perturbation under the existing finite half-ℓ¹ TV API. -/
theorem expectation_sub_le_qFiniteTotalVariation_mul_range
    (p q w : State → ℝ) (lo hi : ℝ)
    (hp : ∑ s, p s = 1) (hq : ∑ s, q s = 1)
    (hwlo : ∀ s, lo ≤ w s) (hwhi : ∀ s, w s ≤ hi) :
    (∑ s, p s * w s) - (∑ s, q s * w s) ≤
      StatisticalRL.QLearning.qFiniteTotalVariation p q * (hi - lo) := by
  classical
  let d : State → ℝ := fun s ↦ p s - q s
  let center : ℝ := (lo + hi) / 2
  let halfRange : ℝ := (hi - lo) / 2
  have hsumd : ∑ s, d s = 0 := by
    simp [d, Finset.sum_sub_distrib, hp, hq]
  have hrepr :
      (∑ s, p s * w s) - (∑ s, q s * w s) =
        ∑ s, d s * (w s - center) := by
    calc
      (∑ s, p s * w s) - (∑ s, q s * w s) =
          ∑ s, (p s * w s - q s * w s) :=
        (Finset.sum_sub_distrib ..).symm
      _ = ∑ s, d s * w s := by
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [d]
        ring
      _ = ∑ s, d s * ((w s - center) + center) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = (∑ s, d s * (w s - center)) + ∑ s, d s * center := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = ∑ s, d s * (w s - center) := by
        rw [← Finset.sum_mul, hsumd]
        simp
  have hrange : 0 ≤ hi - lo := sub_nonneg.mpr (by
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    exact le_trans (hwlo s) (hwhi s))
  have hcenter : ∀ s, |w s - center| ≤ halfRange := by
    intro s
    rw [abs_le]
    dsimp [center, halfRange]
    constructor <;> linarith [hwlo s, hwhi s]
  have hterm : ∀ s, d s * (w s - center) ≤ |d s| * halfRange := by
    intro s
    calc
      d s * (w s - center) ≤ |d s * (w s - center)| := le_abs_self _
      _ = |d s| * |w s - center| := abs_mul _ _
      _ ≤ |d s| * halfRange :=
        mul_le_mul_of_nonneg_left (hcenter s) (abs_nonneg _)
  calc
    (∑ s, p s * w s) - (∑ s, q s * w s)
        = ∑ s, d s * (w s - center) := hrepr
    _ ≤ ∑ s, |d s| * halfRange := Finset.sum_le_sum fun s _ ↦ hterm s
    _ = (∑ s, |d s|) * halfRange := (Finset.sum_mul ..).symm
    _ = StatisticalRL.QLearning.qFiniteTotalVariation p q * (hi - lo) := by
      simp [StatisticalRL.QLearning.qFiniteTotalVariation, d, halfRange]
      ring

/-- TV weak-duality bound for every feasible row and scalar α. Its TV
inequality can be obtained from the source event-TV radius by the bridge in
`Formalization.RobustRL.TVCore`. -/
theorem tv_clipped_weak_duality
    (p q V : State → ℝ) (vmin vmax α σ : ℝ)
    (hp_nonneg : ∀ s, 0 ≤ p s) (hq_nonneg : ∀ s, 0 ≤ q s)
    (hp_sum : ∑ s, p s = 1) (hq_sum : ∑ s, q s = 1)
    (hV_nonneg : ∀ s, 0 ≤ V s)
    (hVmin : ∀ s, vmin ≤ V s) (hVmin_attained : ∃ s, V s = vmin)
    (hVmax : ∀ s, V s ≤ vmax) (hVmin_le_max : vmin ≤ vmax)
    (hσ : 0 < σ) (hαlo : vmin ≤ α) (hαhi : α ≤ vmax)
    (hTV : StatisticalRL.QLearning.qFiniteTotalVariation p q ≤ σ) :
    (∑ s, p s * tvClipAbove V α s) - σ * (α - vmin) ≤
      ∑ s, q s * V s := by
  classical
  let w : State → ℝ := tvClipAbove V α
  have hwlo : ∀ s, vmin ≤ w s := by
    intro s
    dsimp [w, tvClipAbove]
    exact le_min (hVmin s) hαlo
  have hwhi : ∀ s, w s ≤ α := by
    intro s
    dsimp [w, tvClipAbove]
    exact min_le_right _ _
  have hwmin_attained : ∃ s, w s = vmin := by
    obtain ⟨s, hs⟩ := hVmin_attained
    refine ⟨s, ?_⟩
    dsimp [w, tvClipAbove]
    rw [hs]
    exact min_eq_left hαlo
  have hwleV : ∀ s, w s ≤ V s := by
    intro s
    dsimp [w, tvClipAbove]
    exact min_le_left _ _
  have hwidth : 0 ≤ α - vmin := sub_nonneg.mpr hαlo
  have hperturb := expectation_sub_le_qFiniteTotalVariation_mul_range
    p q w vmin α hp_sum hq_sum hwlo hwhi
  have hperturbσ :
      (∑ s, p s * w s) - (∑ s, q s * w s) ≤ σ * (α - vmin) :=
    le_trans hperturb (mul_le_mul_of_nonneg_right hTV hwidth)
  have hqw : (∑ s, q s * w s) ≤ ∑ s, q s * V s :=
    Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hwleV s) (hq_nonneg s)
  dsimp [w] at hperturbσ
  nlinarith

end StatisticalRL.RobustRL
