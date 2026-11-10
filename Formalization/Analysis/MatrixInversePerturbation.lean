import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Quantitative perturbation of `X⁻¹ Y X⁻ᵀ` at an invertible matrix

Generic infrastructure (no RL content). Norms of square real matrices are the `ℓ∞` operator norm
(maximal absolute row sum), Mathlib's `Matrix.linftyOpNormedRing`, enabled as a local instance.

* `isUnit_det_of_norm_inv_mul_norm_sub_lt_one`: if `A` is invertible and `‖A⁻¹‖‖X − A‖ < 1`, then
  `X` is invertible (so Lean's `Matrix.inv` is the genuine inverse of `X`, never the junk `0`).
* `norm_inv_le_two_mul`, `norm_inv_sub_inv_le`: if `‖A⁻¹‖‖X − A‖ ≤ 1/2`, then
  `‖X⁻¹‖ ≤ 2‖A⁻¹‖` and `‖X⁻¹ − A⁻¹‖ ≤ 2‖A⁻¹‖²‖X − A‖`.
* `abs_inv_mul_mul_inv_transpose_sub_le`: an explicit entrywise bound
  `|(X⁻¹YX⁻ᵀ − A⁻¹GA⁻ᵀ)(s,s')| ≤ 6‖A⁻¹‖³ S (g + δY) δX + 2‖A⁻¹‖² δY` when every entry of `X − A`
  is at most `δX`, every entry of `Y − G` at most `δY`, every entry of `G` at most `g`, and
  `S ‖A⁻¹‖ δX ≤ 1/2` (`S` the dimension).
* `abs_inv_sub_inv_apply_le`: the entrywise form `|(X⁻¹ − A⁻¹)(s,s')| ≤ 2‖A⁻¹‖² S δX`.
-/

open Finset
open scoped Matrix

namespace StatisticalRL.Analysis.MatrixInversePerturbation

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An absolute row sum is at most the `ℓ∞` operator norm. -/
theorem sum_abs_le_norm (P : Matrix ι ι ℝ) (i : ι) : ∑ j, |P i j| ≤ ‖P‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i : ι ↦ ∑ j, ‖P i j‖₊) (Finset.mem_univ i)
  calc ∑ j, |P i j| = ((∑ j, ‖P i j‖₊ : NNReal) : ℝ) := by
        simp [NNReal.coe_sum, Real.norm_eq_abs]
    _ ≤ _ := NNReal.coe_le_coe.2 h

/-- Every entry is at most the `ℓ∞` operator norm. -/
theorem abs_apply_le_norm (P : Matrix ι ι ℝ) (i j : ι) : |P i j| ≤ ‖P‖ :=
  (Finset.single_le_sum (f := fun j ↦ |P i j|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ j)).trans (sum_abs_le_norm P i)

/-- Absolute row sums at most `r ≥ 0` bound the `ℓ∞` operator norm by `r`. -/
theorem norm_le_of_sum_abs_le {P : Matrix ι ι ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ∑ j, |P i j| ≤ r) : ‖P‖ ≤ r := by
  rw [Matrix.linfty_opNorm_def]
  lift r to NNReal using hr
  refine NNReal.coe_le_coe.2 (Finset.sup_le fun i _ ↦ ?_)
  refine NNReal.coe_le_coe.1 ?_
  simpa [NNReal.coe_sum, Real.norm_eq_abs] using h i

/-- Entries at most `m ≥ 0` bound the `ℓ∞` operator norm by `card ι * m`. -/
theorem norm_le_card_mul_of_abs_le {P : Matrix ι ι ℝ} {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ i j, |P i j| ≤ m) : ‖P‖ ≤ Fintype.card ι * m := by
  refine norm_le_of_sum_abs_le (by positivity) fun i ↦ ?_
  calc ∑ j, |P i j| ≤ ∑ _j : ι, m := Finset.sum_le_sum fun j _ ↦ h i j
    _ = Fintype.card ι * m := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Invertibility is open, quantitatively.** -/
theorem isUnit_det_of_norm_inv_mul_norm_sub_lt_one {A X : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (h : ‖A⁻¹‖ * ‖X - A‖ < 1) : IsUnit X.det := by
  refine (Matrix.isUnit_iff_isUnit_det X).1 (Matrix.mulVec_injective_iff_isUnit.1 ?_)
  intro v w hvw
  have hu : X *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
  have hrepr : (A⁻¹ * (X - A)) *ᵥ (v - w) = -(v - w) := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hu, zero_sub, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  have hn : ‖v - w‖ ≤ ‖A⁻¹‖ * ‖X - A‖ * ‖v - w‖ := by
    calc ‖v - w‖ = ‖(A⁻¹ * (X - A)) *ᵥ (v - w)‖ := by rw [hrepr, norm_neg]
      _ ≤ ‖A⁻¹ * (X - A)‖ * ‖v - w‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ‖A⁻¹‖ * ‖X - A‖ * ‖v - w‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  have h0 : ‖v - w‖ = 0 := by
    have := norm_nonneg (v - w)
    nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

/-- The resolvent identity `X⁻¹ − A⁻¹ = X⁻¹ (A − X) A⁻¹` for invertible `A`, `X`. -/
theorem inv_sub_inv_eq {A X : Matrix ι ι ℝ} (hA : IsUnit A.det) (hX : IsUnit X.det) :
    X⁻¹ - A⁻¹ = X⁻¹ * (A - X) * A⁻¹ := by
  have : X⁻¹ * (A - X) * A⁻¹ = X⁻¹ * (A * A⁻¹) - X⁻¹ * X * A⁻¹ := by
    rw [mul_sub, sub_mul, mul_assoc]
  rw [this, Matrix.mul_nonsing_inv _ hA, Matrix.nonsing_inv_mul _ hX, mul_one, one_mul]

/-- `‖X⁻¹‖ ≤ 2‖A⁻¹‖` when `‖A⁻¹‖‖X − A‖ ≤ 1/2`. -/
theorem norm_inv_le_two_mul {A X : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (h : ‖A⁻¹‖ * ‖X - A‖ ≤ 1 / 2) : ‖X⁻¹‖ ≤ 2 * ‖A⁻¹‖ := by
  have hX := isUnit_det_of_norm_inv_mul_norm_sub_lt_one hA (h.trans_lt (by norm_num))
  have hid : X⁻¹ = A⁻¹ + X⁻¹ * (A - X) * A⁻¹ := by
    rw [← inv_sub_inv_eq hA hX]; abel
  have hb : ‖X⁻¹‖ ≤ ‖A⁻¹‖ + ‖X⁻¹‖ * (‖A⁻¹‖ * ‖X - A‖) := by
    calc ‖X⁻¹‖ = ‖A⁻¹ + X⁻¹ * (A - X) * A⁻¹‖ := by rw [← hid]
      _ ≤ ‖A⁻¹‖ + ‖X⁻¹ * (A - X) * A⁻¹‖ := norm_add_le _ _
      _ ≤ ‖A⁻¹‖ + ‖X⁻¹‖ * ‖A - X‖ * ‖A⁻¹‖ := by
          gcongr
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖A⁻¹‖ + ‖X⁻¹‖ * (‖A⁻¹‖ * ‖X - A‖) := by rw [norm_sub_rev]; ring
  have := mul_le_mul_of_nonneg_left h (norm_nonneg X⁻¹)
  linarith

/-- `‖X⁻¹ − A⁻¹‖ ≤ 2‖A⁻¹‖²‖X − A‖` when `‖A⁻¹‖‖X − A‖ ≤ 1/2`. -/
theorem norm_inv_sub_inv_le {A X : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (h : ‖A⁻¹‖ * ‖X - A‖ ≤ 1 / 2) : ‖X⁻¹ - A⁻¹‖ ≤ 2 * ‖A⁻¹‖ ^ 2 * ‖X - A‖ := by
  have hX := isUnit_det_of_norm_inv_mul_norm_sub_lt_one hA (h.trans_lt (by norm_num))
  rw [inv_sub_inv_eq hA hX]
  calc ‖X⁻¹ * (A - X) * A⁻¹‖ ≤ ‖X⁻¹‖ * ‖A - X‖ * ‖A⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (2 * ‖A⁻¹‖) * ‖A - X‖ * ‖A⁻¹‖ := by
        gcongr
        exact norm_inv_le_two_mul hA h
    _ = 2 * ‖A⁻¹‖ ^ 2 * ‖X - A‖ := by rw [norm_sub_rev]; ring

/-- `|(P Q Rᵀ)(s,s')| ≤ ‖P‖ m ‖R‖` when every entry of `Q` is at most `m` in absolute value. -/
theorem abs_mul_mul_transpose_apply_le (P Q R : Matrix ι ι ℝ) {m : ℝ}
    (hQ : ∀ i j, |Q i j| ≤ m) (s s' : ι) : |(P * Q * Rᵀ) s s'| ≤ ‖P‖ * m * ‖R‖ := by
  have hm : 0 ≤ m := (abs_nonneg _).trans (hQ s s)
  have hrow : ∀ j, |∑ i, P s i * Q i j| ≤ (∑ i, |P s i|) * m := fun j ↦ by
    calc |∑ i, P s i * Q i j| ≤ ∑ i, |P s i * Q i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |P s i| * m := Finset.sum_le_sum fun i _ ↦ by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hQ i j) (abs_nonneg _)
      _ = (∑ i, |P s i|) * m := by rw [Finset.sum_mul]
  have hP := sum_abs_le_norm P s
  have hR := sum_abs_le_norm R s'
  have hPs : 0 ≤ ∑ i, |P s i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hRs : 0 ≤ ∑ j, |R s' j| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc |∑ j, (∑ i, P s i * Q i j) * R s' j| ≤ ∑ j, |∑ i, P s i * Q i j| * |R s' j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ ≤ ∑ j, (∑ i, |P s i|) * m * |R s' j| :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hrow j) (abs_nonneg _)
    _ = (∑ i, |P s i|) * m * ∑ j, |R s' j| := by rw [Finset.mul_sum]
    _ ≤ ‖P‖ * m * ‖R‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hP hm) hR hRs
          (mul_nonneg ((norm_nonneg _)) hm)

/-- Entrywise closeness with `S ‖A⁻¹‖ δX ≤ 1/2` gives `‖A⁻¹‖ ‖X − A‖ ≤ 1/2`. -/
theorem norm_inv_mul_norm_sub_le_half {A X : Matrix ι ι ℝ} {δX : ℝ} (hδX : 0 ≤ δX)
    (hX : ∀ i j, |X i j - A i j| ≤ δX) (hsmall : Fintype.card ι * ‖A⁻¹‖ * δX ≤ 1 / 2) :
    ‖A⁻¹‖ * ‖X - A‖ ≤ 1 / 2 := by
  have hd : ‖X - A‖ ≤ Fintype.card ι * δX :=
    norm_le_card_mul_of_abs_le hδX fun i j ↦ by simpa only [Matrix.sub_apply] using hX i j
  calc ‖A⁻¹‖ * ‖X - A‖ ≤ ‖A⁻¹‖ * (Fintype.card ι * δX) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = Fintype.card ι * ‖A⁻¹‖ * δX := by ring
    _ ≤ 1 / 2 := hsmall

/-- Entrywise closeness with `S ‖A⁻¹‖ δX ≤ 1/2` forces `X` invertible. -/
theorem isUnit_det_of_abs_sub_le {A X : Matrix ι ι ℝ} (hA : IsUnit A.det) {δX : ℝ}
    (hδX : 0 ≤ δX) (hX : ∀ i j, |X i j - A i j| ≤ δX)
    (hsmall : Fintype.card ι * ‖A⁻¹‖ * δX ≤ 1 / 2) : IsUnit X.det :=
  isUnit_det_of_norm_inv_mul_norm_sub_lt_one hA
    ((norm_inv_mul_norm_sub_le_half hδX hX hsmall).trans_lt (by norm_num))

/-- **Entrywise inverse perturbation.** If every entry of `X − A` is at most `δX` and
`S ‖A⁻¹‖ δX ≤ 1/2`, then `|(X⁻¹ − A⁻¹)(s,s')| ≤ 2‖A⁻¹‖² S δX`. -/
theorem abs_inv_sub_inv_apply_le {A X : Matrix ι ι ℝ} (hA : IsUnit A.det) {δX : ℝ}
    (hX : ∀ i j, |X i j - A i j| ≤ δX) (hsmall : Fintype.card ι * ‖A⁻¹‖ * δX ≤ 1 / 2)
    (s s' : ι) : |X⁻¹ s s' - A⁻¹ s s'| ≤ 2 * ‖A⁻¹‖ ^ 2 * Fintype.card ι * δX := by
  have hδX : 0 ≤ δX := (abs_nonneg _).trans (hX s s)
  have hh := norm_inv_mul_norm_sub_le_half hδX hX hsmall
  have hd : ‖X - A‖ ≤ Fintype.card ι * δX :=
    norm_le_card_mul_of_abs_le hδX fun i j ↦ by simpa only [Matrix.sub_apply] using hX i j
  calc |X⁻¹ s s' - A⁻¹ s s'| = |(X⁻¹ - A⁻¹) s s'| := by rw [Matrix.sub_apply]
    _ ≤ ‖X⁻¹ - A⁻¹‖ := abs_apply_le_norm _ _ _
    _ ≤ 2 * ‖A⁻¹‖ ^ 2 * ‖X - A‖ := norm_inv_sub_inv_le hA hh
    _ ≤ 2 * ‖A⁻¹‖ ^ 2 * (Fintype.card ι * δX) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 2 * ‖A⁻¹‖ ^ 2 * Fintype.card ι * δX := by ring

/-- **Quantitative perturbation of `X⁻¹ Y X⁻ᵀ`** (replaces a continuity argument). If `A` is
invertible, every entry of `G` is at most `g`, every entry of `X − A` at most `δX`, every entry
of `Y − G` at most `δY`, and `S ‖A⁻¹‖ δX ≤ 1/2` (`S = card ι`), then for every `(s,s')`,
`|(X⁻¹YX⁻ᵀ)(s,s') − (A⁻¹GA⁻ᵀ)(s,s')| ≤ 6‖A⁻¹‖³ S (g + δY) δX + 2‖A⁻¹‖² δY`.
Under these hypotheses `X` is invertible (`isUnit_det_of_abs_sub_le`), so `X⁻¹` is the genuine
inverse. -/
theorem abs_inv_mul_mul_inv_transpose_sub_le {A G X Y : Matrix ι ι ℝ} (hA : IsUnit A.det)
    {g δX δY : ℝ} (hG : ∀ i j, |G i j| ≤ g) (hX : ∀ i j, |X i j - A i j| ≤ δX)
    (hY : ∀ i j, |Y i j - G i j| ≤ δY) (hsmall : Fintype.card ι * ‖A⁻¹‖ * δX ≤ 1 / 2)
    (s s' : ι) :
    |(X⁻¹ * Y * X⁻¹ᵀ) s s' - (A⁻¹ * G * A⁻¹ᵀ) s s'| ≤
      6 * ‖A⁻¹‖ ^ 3 * Fintype.card ι * (g + δY) * δX + 2 * ‖A⁻¹‖ ^ 2 * δY := by
  have hδX : 0 ≤ δX := (abs_nonneg _).trans (hX s s)
  have hδY : 0 ≤ δY := (abs_nonneg _).trans (hY s s)
  have hg : 0 ≤ g := (abs_nonneg _).trans (hG s s)
  have hh := norm_inv_mul_norm_sub_le_half hδX hX hsmall
  set a := ‖A⁻¹‖ with ha_def
  have ha : 0 ≤ a := norm_nonneg _
  set d := ‖X - A‖ with hd_def
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd : d ≤ Fintype.card ι * δX :=
    norm_le_card_mul_of_abs_le hδX fun i j ↦ by simpa only [Matrix.sub_apply] using hX i j
  have hXi : ‖X⁻¹‖ ≤ 2 * a := norm_inv_le_two_mul hA hh
  have hD : ‖X⁻¹ - A⁻¹‖ ≤ 2 * a ^ 2 * d := norm_inv_sub_inv_le hA hh
  have hYb : ∀ i j, |Y i j| ≤ g + δY := fun i j ↦ by
    have := abs_sub_abs_le_abs_sub (Y i j) (G i j)
    linarith [hG i j, hY i j]
  have hYG : ∀ i j, |(Y - G) i j| ≤ δY := fun i j ↦ by
    simpa only [Matrix.sub_apply] using hY i j
  have hdec : X⁻¹ * Y * X⁻¹ᵀ - A⁻¹ * G * A⁻¹ᵀ =
      (X⁻¹ - A⁻¹) * Y * X⁻¹ᵀ + A⁻¹ * (Y - G) * X⁻¹ᵀ + A⁻¹ * G * (X⁻¹ - A⁻¹)ᵀ := by
    simp only [Matrix.transpose_sub, sub_mul, mul_sub]
    abel
  have h1 := abs_mul_mul_transpose_apply_le (X⁻¹ - A⁻¹) Y X⁻¹ hYb s s'
  have h2 := abs_mul_mul_transpose_apply_le A⁻¹ (Y - G) X⁻¹ hYG s s'
  have h3 := abs_mul_mul_transpose_apply_le A⁻¹ G (X⁻¹ - A⁻¹) hG s s'
  have hgY : 0 ≤ g + δY := by linarith
  have b1 : ‖X⁻¹ - A⁻¹‖ * (g + δY) * ‖X⁻¹‖ ≤ (2 * a ^ 2 * d) * (g + δY) * (2 * a) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hD hgY) hXi (norm_nonneg _) (by positivity)
  have b2 : a * δY * ‖X⁻¹‖ ≤ a * δY * (2 * a) :=
    mul_le_mul_of_nonneg_left hXi (by positivity)
  have b3 : a * g * ‖X⁻¹ - A⁻¹‖ ≤ a * g * (2 * a ^ 2 * d) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hfin : 4 * a ^ 3 * d * (g + δY) + 2 * a ^ 2 * δY + 2 * a ^ 3 * g * d ≤
      6 * a ^ 3 * Fintype.card ι * (g + δY) * δX + 2 * a ^ 2 * δY := by
    have e1 : a ^ 3 * g * d ≤ a ^ 3 * (g + δY) * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hd0
    have e2 : a ^ 3 * (g + δY) * d ≤ a ^ 3 * (g + δY) * (Fintype.card ι * δX) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    linarith
  calc |(X⁻¹ * Y * X⁻¹ᵀ) s s' - (A⁻¹ * G * A⁻¹ᵀ) s s'|
      = |((X⁻¹ - A⁻¹) * Y * X⁻¹ᵀ) s s' + (A⁻¹ * (Y - G) * X⁻¹ᵀ) s s' +
          (A⁻¹ * G * (X⁻¹ - A⁻¹)ᵀ) s s'| := by
        rw [← Matrix.sub_apply, hdec, Matrix.add_apply, Matrix.add_apply]
    _ ≤ |((X⁻¹ - A⁻¹) * Y * X⁻¹ᵀ) s s'| + |(A⁻¹ * (Y - G) * X⁻¹ᵀ) s s'| +
          |(A⁻¹ * G * (X⁻¹ - A⁻¹)ᵀ) s s'| := abs_add_three _ _ _
    _ ≤ 4 * a ^ 3 * d * (g + δY) + 2 * a ^ 2 * δY + 2 * a ^ 3 * g * d := by
        linarith
    _ ≤ _ := hfin

end StatisticalRL.Analysis.MatrixInversePerturbation
