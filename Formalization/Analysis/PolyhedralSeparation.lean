import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite polyhedral representation of a convex set

Infrastructure (not a source result). On `κ → ℝ` with Mathlib's sup norm, write
`⟨v, x⟩ = ∑ j, v j * x j` and `|v|₁ = ∑ j, |v j|`. For a nonempty finite family
`𝓕 : Finset ((κ → ℝ) × ℝ)` the *polyhedral function* is

`x ↦ 𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * x j - q.2)`,

the maximum of the affine forms `x ↦ ⟨q.1, x⟩ - q.2`. All statements below are written with this
explicit `Finset.sup'` expression (no separate definition), so they can be consumed by any file
that defines the same function.

* `exists_normalized_separator`: a point `y ∉ C` of a convex set `C` is strictly separated from
  the finite set `C ∩ P` by an affine form with `|v|₁ = 1`.
* `exists_polyhedral_repr`: for convex `C` and finite `P` containing a point outside `C`, there is
  a nonempty family of `|·|₁`-normalised affine forms whose maximum `φ` satisfies
  `φ y ≤ 0 ↔ y ∈ C` for every `y ∈ P`; moreover every form is strictly negative on `C ∩ P`, and
  `φ y > 0` for `y ∈ P \ C`. The set `C` need not be closed or measurable.
* `abs_sup'_affine_sub_le`: if every form has `|q.1|₁ = 1`, the polyhedral function is
  `1`-Lipschitz for the sup norm: `|φ x - φ y| ≤ ‖x - y‖`.
* `convexOn_sup'_affine`: the polyhedral function is convex.

The separation uses `geometric_hahn_banach_closed_point` on the convex hull of `C ∩ P`, which is
compact because `C ∩ P` is finite.
-/

open Finset

namespace StatisticalRL.Analysis.PolyhedralSeparation

variable {κ : Type*} [Fintype κ]

/-- `|⟨u, w⟩| ≤ |u|₁ ‖w‖` for the sup norm. -/
theorem abs_sum_mul_le_sum_abs_mul_norm (u w : κ → ℝ) :
    |∑ j, u j * w j| ≤ (∑ j, |u j|) * ‖w‖ := by
  calc |∑ j, u j * w j| ≤ ∑ j, |u j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |u j| * ‖w‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w j) (abs_nonneg _)
    _ = (∑ j, |u j|) * ‖w‖ := by rw [Finset.sum_mul]

/-- A continuous linear form on `κ → ℝ` is the dot product with its values on the standard
basis. -/
theorem strongDual_apply_eq_sum [DecidableEq κ] (f : StrongDual ℝ (κ → ℝ)) (x : κ → ℝ) :
    f x = ∑ j, f (fun k ↦ if j = k then 1 else 0) * x j := by
  have h := LinearMap.pi_apply_eq_sum_univ f.toLinearMap x
  rw [show f x = f.toLinearMap x from rfl, h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul, mul_comm]
  rfl

/-- Strict separation of a point outside a convex set `C` from the finite set `C ∩ P` by an
affine form `z ↦ ⟨q.1, z⟩ - q.2` with `|q.1|₁ = 1`. When `C ∩ P = ∅` a coordinate form is
used. -/
theorem exists_normalized_separator [Nonempty κ] {C : Set (κ → ℝ)} (hC : Convex ℝ C)
    (P : Finset (κ → ℝ)) {y : κ → ℝ} (hy : y ∉ C) :
    ∃ q : (κ → ℝ) × ℝ, ∑ j, |q.1 j| = 1 ∧
      (∀ z ∈ P, z ∈ C → ∑ j, q.1 j * z j - q.2 < 0) ∧ 0 < ∑ j, q.1 j * y j - q.2 := by
  classical
  by_cases hempty : ∀ z ∈ P, z ∉ C
  · obtain ⟨j₀⟩ := (inferInstance : Nonempty κ)
    refine ⟨(Pi.single j₀ 1, y j₀ - 1), ?_, fun z hz hzC ↦ absurd hzC (hempty z hz), ?_⟩
    · simp only [Pi.single_apply]
      rw [Finset.sum_eq_single j₀ (fun b _ hb ↦ by simp [hb]) (by simp)]
      simp
    · simp [Pi.single_apply]
  push_neg at hempty
  obtain ⟨z₀, hz₀P, hz₀C⟩ := hempty
  set K : Set (κ → ℝ) := convexHull ℝ ((P : Set (κ → ℝ)) ∩ C) with hKdef
  have hfin : ((P : Set (κ → ℝ)) ∩ C).Finite := P.finite_toSet.inter_of_left C
  have hKclosed : IsClosed K := hfin.isCompact_convexHull.isClosed
  have hKsub : K ⊆ C := convexHull_min Set.inter_subset_right hC
  have hyK : y ∉ K := fun h ↦ hy (hKsub h)
  have hz₀K : z₀ ∈ K := subset_convexHull ℝ _ ⟨hz₀P, hz₀C⟩
  obtain ⟨f, u, hfK, hfy⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hKclosed hyK
  set g : κ → ℝ := fun j ↦ f (fun k ↦ if j = k then 1 else 0) with hg
  have hf : ∀ x, f x = ∑ j, g j * x j := fun x ↦ strongDual_apply_eq_sum f x
  set s : ℝ := ∑ j, |g j| with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hspos : 0 < s := by
    refine lt_of_le_of_ne hs0 fun h ↦ ?_
    have hg0 : ∀ j, g j = 0 := fun j ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg (g j)).1 h.symm j
        (Finset.mem_univ j)
      exact abs_eq_zero.1 this
    have h1 := hfK z₀ hz₀K
    rw [hf] at h1 hfy
    simp only [hg0, zero_mul, Finset.sum_const_zero] at h1 hfy
    linarith
  refine ⟨(fun j ↦ g j / s, u / s), ?_, ?_, ?_⟩
  · simp only [abs_div, abs_of_pos hspos]
    rw [← Finset.sum_div, ← hs, div_self hspos.ne']
  · intro z hzP hzC
    have h1 := hfK z (subset_convexHull ℝ _ ⟨hzP, hzC⟩)
    rw [hf] at h1
    have : ∑ j, g j / s * z j - u / s = (∑ j, g j * z j - u) / s := by
      rw [sub_div, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    simp only
    rw [this]
    exact div_neg_of_neg_of_pos (by linarith) hspos
  · rw [hf] at hfy
    have : ∑ j, g j / s * y j - u / s = (∑ j, g j * y j - u) / s := by
      rw [sub_div, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    simp only
    rw [this]
    exact div_pos (by linarith) hspos

/-- **Finite polyhedral representation.** For a convex `C ⊆ κ → ℝ` (not necessarily closed) and
a finite `P` containing a point `y₀ ∉ C`, there is a nonempty finite family `𝓕` of affine forms
`x ↦ ⟨q.1, x⟩ - q.2` with `|q.1|₁ = 1` such that every form is strictly negative on `C ∩ P`,
the maximum `φ` of the forms is positive on `P \ C`, and hence `φ y ≤ 0 ↔ y ∈ C` for `y ∈ P`. -/
theorem exists_polyhedral_repr [Nonempty κ] {C : Set (κ → ℝ)} (hC : Convex ℝ C)
    (P : Finset (κ → ℝ)) {y₀ : κ → ℝ} (hy₀P : y₀ ∈ P) (hy₀C : y₀ ∉ C) :
    ∃ (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty),
      (∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) ∧
      (∀ q ∈ 𝓕, ∀ z ∈ P, z ∈ C → ∑ j, q.1 j * z j - q.2 < 0) ∧
      (∀ y ∈ P, y ∉ C → 0 < 𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * y j - q.2)) ∧
      ∀ y ∈ P, (𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * y j - q.2) ≤ 0 ↔ y ∈ C) := by
  classical
  let sep : (κ → ℝ) → (κ → ℝ) × ℝ := fun y ↦
    if h : y ∈ C then (0, 0) else Classical.choose (exists_normalized_separator hC P h)
  have hsep : ∀ y, y ∉ C → (∑ j, |(sep y).1 j| = 1 ∧
      (∀ z ∈ P, z ∈ C → ∑ j, (sep y).1 j * z j - (sep y).2 < 0) ∧
      0 < ∑ j, (sep y).1 j * y j - (sep y).2) := by
    intro y hy
    simp only [sep, dif_neg hy]
    exact Classical.choose_spec (exists_normalized_separator hC P hy)
  set 𝓕 := (P.filter (· ∉ C)).image sep with h𝓕def
  have hmem : ∀ q ∈ 𝓕, ∃ y ∈ P, y ∉ C ∧ sep y = q := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨hyP, hyC⟩ := Finset.mem_filter.1 hy
    exact ⟨y, hyP, hyC, rfl⟩
  have hin : ∀ y ∈ P, y ∉ C → sep y ∈ 𝓕 := fun y hyP hyC ↦
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hyP, hyC⟩)
  have hne : 𝓕.Nonempty := ⟨_, hin y₀ hy₀P hy₀C⟩
  have hneg : ∀ q ∈ 𝓕, ∀ z ∈ P, z ∈ C → ∑ j, q.1 j * z j - q.2 < 0 := by
    intro q hq
    obtain ⟨y, -, hyC, rfl⟩ := hmem q hq
    exact (hsep y hyC).2.1
  have hpos : ∀ y ∈ P, y ∉ C → 0 < 𝓕.sup' hne (fun q ↦ ∑ j, q.1 j * y j - q.2) := by
    intro y hyP hyC
    exact lt_of_lt_of_le (hsep y hyC).2.2
      (Finset.le_sup' (fun q : (κ → ℝ) × ℝ ↦ ∑ j, q.1 j * y j - q.2) (hin y hyP hyC))
  refine ⟨𝓕, hne, ?_, hneg, hpos, ?_⟩
  · intro q hq
    obtain ⟨y, -, hyC, rfl⟩ := hmem q hq
    exact (hsep y hyC).1
  · intro y hyP
    constructor
    · intro hle
      by_contra hyC
      exact absurd hle (not_le.2 (hpos y hyP hyC))
    · intro hyC
      exact Finset.sup'_le _ _ fun q hq ↦ (hneg q hq y hyP hyC).le

/-- The maximum of finitely many affine forms with `|q.1|₁ = 1` is `1`-Lipschitz for the sup
norm. -/
theorem abs_sup'_affine_sub_le (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty)
    (hnorm : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) (x y : κ → ℝ) :
    |𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * x j - q.2) -
      𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * y j - q.2)| ≤ ‖x - y‖ := by
  have key : ∀ a b : κ → ℝ,
      𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * a j - q.2) ≤
        𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * b j - q.2) + ‖a - b‖ := by
    intro a b
    refine Finset.sup'_le _ _ fun q hq ↦ ?_
    have h1 := abs_sum_mul_le_sum_abs_mul_norm q.1 (a - b)
    rw [hnorm q hq, one_mul] at h1
    have hsplit : ∑ j, q.1 j * (a - b) j = ∑ j, q.1 j * a j - ∑ j, q.1 j * b j := by
      simp [mul_sub, Finset.sum_sub_distrib]
    rw [hsplit] at h1
    have h2 := Finset.le_sup' (fun q : (κ → ℝ) × ℝ ↦ ∑ j, q.1 j * b j - q.2) hq
    simp only at h2 ⊢
    linarith [le_abs_self (∑ j, q.1 j * a j - ∑ j, q.1 j * b j)]
  rw [abs_sub_le_iff]
  constructor
  · linarith [key x y]
  · linarith [key y x, norm_sub_rev x y]

/-- The maximum of finitely many affine forms is convex. -/
theorem convexOn_sup'_affine (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) :
    ConvexOn ℝ Set.univ (fun x : κ → ℝ ↦ 𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * x j - q.2)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  refine Finset.sup'_le _ _ fun q hq ↦ ?_
  have hx := Finset.le_sup' (fun q : (κ → ℝ) × ℝ ↦ ∑ j, q.1 j * x j - q.2) hq
  have hy := Finset.le_sup' (fun q : (κ → ℝ) × ℝ ↦ ∑ j, q.1 j * y j - q.2) hq
  simp only at hx hy
  have hs : ∑ j, q.1 j * (a • x + b • y) j =
      a * ∑ j, q.1 j * x j + b * ∑ j, q.1 j * y j := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hlin : ∑ j, q.1 j * (a • x + b • y) j - q.2 =
      a * (∑ j, q.1 j * x j - q.2) + b * (∑ j, q.1 j * y j - q.2) := by
    rw [hs]
    linear_combination q.2 * hab
  simp only [smul_eq_mul]
  rw [hlin]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

end StatisticalRL.Analysis.PolyhedralSeparation
