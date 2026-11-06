import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Scalar Bernoulli Pinsker inequality

`2 (p - q)^2 ≤ KL(p ‖ q)` for the scalar Bernoulli KL expression
`eq:defn-KL-bern` (`chapters/prelim.tex:1323–1329`) on the open unit square.
Infrastructure for the binary clause of `lem:fano` (`prelim.tex:1140–1152`);
this is not a claim that Lemma 2.10 is complete.

Mathlib-only proof of the interior scalar inequality; boundary law cases are separate obligations.
-/

open Set

namespace StatisticalRL.GenerativeLowerBound

/-- `KL(p ‖ t) - 2 (p - t)^2`, written with separated logarithms, as a function
of the second argument `t`. -/
noncomputable def bernoulliPinskerGap (p t : ℝ) : ℝ :=
  p * (Real.log p - Real.log t) + (1 - p) * (Real.log (1 - p) - Real.log (1 - t)) -
    2 * (p - t) ^ 2

theorem hasDerivAt_bernoulliPinskerGap (p t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (bernoulliPinskerGap p) ((t - p) * (2 * t - 1) ^ 2 / (t * (1 - t))) t := by
  have ht1' : (1 : ℝ) - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  have hlog := (hasDerivAt_id t).log (ne_of_gt ht)
  have hone := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have hlogone := hone.log ht1'
  have hsq := ((hasDerivAt_const t p).sub (hasDerivAt_id t)).pow 2
  have h := (((hasDerivAt_const t p).mul ((hasDerivAt_const t (Real.log p)).sub hlog)).add
      ((hasDerivAt_const t (1 - p)).mul
        ((hasDerivAt_const t (Real.log (1 - p))).sub hlogone))).sub
      ((hasDerivAt_const t (2 : ℝ)).mul hsq)
  convert h using 1
  simp only [id, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem bernoulliPinskerGap_self (p : ℝ) : bernoulliPinskerGap p p = 0 := by
  simp [bernoulliPinskerGap]

/-- The gap is nonnegative on the open unit square. -/
theorem bernoulliPinskerGap_nonneg (p q : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ bernoulliPinskerGap p q := by
  rcases le_total q p with hqp | hpq
  · have hanti : AntitoneOn (bernoulliPinskerGap p) (Icc q p) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc q p)
      · intro t ht
        exact (hasDerivAt_bernoulliPinskerGap p t (hq.trans_le ht.1)
          (ht.2.trans_lt hp1)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hasDerivAt_bernoulliPinskerGap p t (hq.trans ht.1)
          (ht.2.trans hp1)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have h1 : 0 < t := hq.trans ht.1
        have h2 : t < 1 := ht.2.trans hp1
        rw [(hasDerivAt_bernoulliPinskerGap p t h1 h2).deriv]
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (sq_nonneg _)
        · exact (mul_pos h1 (sub_pos.mpr h2)).le
    have h := hanti ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
    rw [bernoulliPinskerGap_self] at h
    exact h
  · have hmono : MonotoneOn (bernoulliPinskerGap p) (Icc p q) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc p q)
      · intro t ht
        exact (hasDerivAt_bernoulliPinskerGap p t (hp.trans_le ht.1)
          (ht.2.trans_lt hq1)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hasDerivAt_bernoulliPinskerGap p t (hp.trans ht.1)
          (ht.2.trans hq1)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have h1 : 0 < t := hp.trans ht.1
        have h2 : t < 1 := ht.2.trans hq1
        rw [(hasDerivAt_bernoulliPinskerGap p t h1 h2).deriv]
        apply div_nonneg
        · exact mul_nonneg (by linarith [ht.1]) (sq_nonneg _)
        · exact (mul_pos h1 (sub_pos.mpr h2)).le
    have h := hmono ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
    rw [bernoulliPinskerGap_self] at h
    exact h

/-- Scalar Bernoulli Pinsker inequality (frozen signature). -/
theorem bernoulliKLExpression_quadratic_lower (p q : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    2 * (p - q)^2 ≤
      p * Real.log (p / q) + (1-p) * Real.log ((1-p)/(1-q)) := by
  have hgap := bernoulliPinskerGap_nonneg p q hp hp1 hq hq1
  have heq : bernoulliPinskerGap p q =
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) - 2 * (p - q) ^ 2 := by
    unfold bernoulliPinskerGap
    rw [Real.log_div hp.ne' hq.ne', Real.log_div (sub_pos.2 hp1).ne' (sub_pos.2 hq1).ne']
  linarith

end StatisticalRL.GenerativeLowerBound
