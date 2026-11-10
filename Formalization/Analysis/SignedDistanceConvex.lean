import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue

/-!
# The signed distance to a convex set

Infrastructure (milestone M2 of the plan for removing the logarithm from the all-convex route of
Theorem 7.11, `thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`).
This file states no source result.

**Carrier.** Any real normed space `E` (`NormedAddCommGroup E`, `NormedSpace ℝ E`). No inner product
is used, so every statement applies verbatim to `ι → ℝ` with Mathlib's default **sup norm** (the
carrier of `ConvexSmoothIndicator.lean` and `TDInferenceConvexAll711.lean`) and to `EuclideanSpace ℝ ι`.
In particular convexity of the signed distance holds for the sup norm (and every other norm); it is
not a Euclidean phenomenon.

**Definition and conventions.** `signedDist C x = infDist x C - infDist x Cᶜ`. Since `infDist x ∅ = 0`
in Mathlib, the degenerate cases are:
* `C = ∅`: `signedDist ∅ = 0` (`signedDist_empty`);
* `C = univ`: `signedDist univ = 0` (`signedDist_univ`).
These are the only junk values: for `C` nonempty with `Cᶜ` nonempty, `signedDist C x` is `infDist x C`
for `x ∉ C` and `-infDist x Cᶜ` for `x ∈ C`, it is `≤ 0` exactly on `closure C`, `< 0` exactly on
`interior C`, and `= 0` exactly on `frontier C`. On the boundary of a non-closed set nothing special
happens: both distances vanish there. The theorems below carry exactly the nonemptiness hypotheses
they need (none for Lipschitz/convexity, which also hold in the degenerate cases).

**Main results.**
* `lipschitzWith_signedDist`: `signedDist C` is `1`-Lipschitz, for every set `C`.
* `convexOn_signedDist`: for convex `C` (closed or not), `signedDist C` is convex on `univ`.
* `setOf_signedDist_le_of_nonneg`: `{x | signedDist C x ≤ t} = cthickening t C` for `t ≥ 0`.
* `setOf_signedDist_le_of_neg`: `{x | signedDist C x ≤ t} = {x | closedBall x (-t) ⊆ C}` for `t < 0`
  and closed `C` (the inner parallel set of `TDInferenceConvexAll711.lean`).
* `setOf_abs_signedDist_le`: `{x | |signedDist C x| ≤ t} = cthickening t C ∩ cthickening t (interior C)ᶜ`,
  the `t`-shell used in `TDInferenceConvexAll711.lean`.
* convexity of sublevel sets, monotonicity in `C`, continuity and measurability.
-/

open Metric Set

noncomputable section

namespace StatisticalRL.Analysis.SignedDistance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The signed distance to `C`: `infDist x C - infDist x Cᶜ`. It is `infDist x C` off `C` and
`-infDist x Cᶜ` on `C`. For `C = ∅` and `C = univ` it is identically `0`. -/
def signedDist (C : Set E) (x : E) : ℝ := infDist x C - infDist x Cᶜ

variable {C D : Set E} {x y : E}

omit [NormedSpace ℝ E] in
theorem signedDist_of_mem (hx : x ∈ C) : signedDist C x = -infDist x Cᶜ := by
  simp [signedDist, infDist_zero_of_mem hx]

omit [NormedSpace ℝ E] in
theorem signedDist_of_notMem (hx : x ∉ C) : signedDist C x = infDist x C := by
  simp [signedDist, infDist_zero_of_mem (show x ∈ Cᶜ from hx)]

omit [NormedSpace ℝ E] in
theorem signedDist_le_infDist (C : Set E) (x : E) : signedDist C x ≤ infDist x C := by
  have := infDist_nonneg (x := x) (s := Cᶜ); unfold signedDist; linarith

omit [NormedSpace ℝ E] in
theorem neg_infDist_compl_le_signedDist (C : Set E) (x : E) :
    -infDist x Cᶜ ≤ signedDist C x := by
  have := infDist_nonneg (x := x) (s := C); unfold signedDist; linarith

omit [NormedSpace ℝ E] in
theorem signedDist_nonpos_of_mem (hx : x ∈ C) : signedDist C x ≤ 0 := by
  rw [signedDist_of_mem hx]; exact neg_nonpos.2 infDist_nonneg

omit [NormedSpace ℝ E] in
theorem signedDist_nonneg_of_notMem (hx : x ∉ C) : 0 ≤ signedDist C x := by
  rw [signedDist_of_notMem hx]; exact infDist_nonneg

omit [NormedSpace ℝ E] in
@[simp] theorem signedDist_empty : signedDist (∅ : Set E) = 0 := by
  funext x; simp [signedDist, infDist_zero_of_mem (mem_univ x)]

omit [NormedSpace ℝ E] in
@[simp] theorem signedDist_univ : signedDist (univ : Set E) = 0 := by
  funext x; simp [signedDist, infDist_zero_of_mem (mem_univ x)]

omit [NormedSpace ℝ E] in
/-- Complementation flips the sign. -/
theorem signedDist_compl (C : Set E) (x : E) : signedDist Cᶜ x = -signedDist C x := by
  simp only [signedDist, compl_compl]; ring

/-! ## Lipschitz continuity -/

/-- If `x ∈ C` and `y ∉ C`, then `infDist y C + infDist x Cᶜ ≤ dist x y` (a boundary point lies on the
segment `[x, y]`, found by the intermediate value theorem). -/
theorem infDist_add_infDist_compl_le_dist (hx : x ∈ C) (hy : y ∉ C) :
    infDist y C + infDist x Cᶜ ≤ dist x y := by
  set p : ℝ → E := fun θ => (1 - θ) • x + θ • y with hp
  have hpc : Continuous p := by
    rw [hp]; fun_prop
  set φ : ℝ → ℝ := fun θ => signedDist C (p θ) with hφ
  have hφc : Continuous φ :=
    ((continuous_infDist_pt C).comp hpc).sub ((continuous_infDist_pt Cᶜ).comp hpc)
  have h0 : φ 0 ≤ 0 := by
    simp only [hφ, hp, sub_zero, one_smul, zero_smul, add_zero]
    exact signedDist_nonpos_of_mem hx
  have h1 : 0 ≤ φ 1 := by
    simp only [hφ, hp, sub_self, zero_smul, one_smul, zero_add]
    exact signedDist_nonneg_of_notMem hy
  obtain ⟨θ, hθ, hθ0⟩ :=
    intermediate_value_Icc zero_le_one hφc.continuousOn (show (0 : ℝ) ∈ Icc (φ 0) (φ 1) from ⟨h0, h1⟩)
  have hboth : infDist (p θ) C = 0 ∧ infDist (p θ) Cᶜ = 0 := by
    have heq : infDist (p θ) C = infDist (p θ) Cᶜ := by
      have := hθ0; simp only [hφ, signedDist] at this; linarith
    by_cases hm : p θ ∈ C
    · have := infDist_zero_of_mem hm; exact ⟨this, heq ▸ this⟩
    · have := infDist_zero_of_mem (show p θ ∈ Cᶜ from hm); exact ⟨heq ▸ this, this⟩
  have hseg : p θ ∈ segment ℝ x y := by
    rw [segment_eq_image]; exact ⟨θ, hθ, rfl⟩
  have hsum := dist_add_dist_of_mem_segment hseg
  have h2 : infDist y C ≤ dist y (p θ) := by
    have := infDist_le_infDist_add_dist (x := y) (y := p θ) (s := C); linarith [hboth.1]
  have h3 : infDist x Cᶜ ≤ dist x (p θ) := by
    have := infDist_le_infDist_add_dist (x := x) (y := p θ) (s := Cᶜ); linarith [hboth.2]
  rw [dist_comm y] at h2
  linarith

/-- The signed distance is `1`-Lipschitz, for every set `C`. -/
theorem lipschitzWith_signedDist (C : Set E) : LipschitzWith 1 (signedDist C) := by
  refine LipschitzWith.of_le_add fun x y => ?_
  by_cases hx : x ∈ C
  · rw [signedDist_of_mem hx]
    have h1 := infDist_le_infDist_add_dist (x := y) (y := x) (s := Cᶜ)
    have h2 := neg_infDist_compl_le_signedDist C y
    rw [dist_comm y x] at h1
    linarith
  · rw [signedDist_of_notMem hx]
    by_cases hy : y ∈ C
    · rw [signedDist_of_mem hy]
      have := infDist_add_infDist_compl_le_dist hy hx
      rw [dist_comm y x] at this
      linarith
    · rw [signedDist_of_notMem hy]
      exact infDist_le_infDist_add_dist

theorem abs_signedDist_sub_le (C : Set E) (x y : E) :
    |signedDist C x - signedDist C y| ≤ dist x y := by
  have := (lipschitzWith_signedDist C).dist_le_mul x y
  simpa [Real.dist_eq] using this

theorem continuous_signedDist (C : Set E) : Continuous (signedDist C) :=
  (lipschitzWith_signedDist C).continuous

theorem measurable_signedDist [MeasurableSpace E] [OpensMeasurableSpace E] (C : Set E) :
    Measurable (signedDist C) :=
  (continuous_signedDist C).measurable

/-! ## Ball witnesses and convexity -/

/-- If a closed ball `closedBall c ρ` (`ρ ≥ 0`) lies in `C`, `Cᶜ` is nonempty, and
`dist x c ≤ ρ + s`, then `signedDist C x ≤ s`. -/
theorem signedDist_le_of_closedBall_subset (hCc : Cᶜ.Nonempty) {c : E} {ρ s : ℝ} (hρ : 0 ≤ ρ)
    (hball : closedBall c ρ ⊆ C) (hd : dist x c ≤ ρ + s) : signedDist C x ≤ s := by
  rcases lt_or_ge s 0 with hs | hs
  · have hsub : closedBall x (-s) ⊆ C :=
      (closedBall_subset_closedBall' (by linarith)).trans hball
    have hxC : x ∈ C := hsub (mem_closedBall_self (by linarith))
    rw [signedDist_of_mem hxC]
    have : -s ≤ infDist x Cᶜ := by
      refine (le_infDist hCc).2 fun q hq => ?_
      by_contra hlt
      exact hq (hsub (mem_closedBall.2 (by rw [dist_comm]; exact le_of_lt (lt_of_not_ge hlt))))
    linarith
  · by_cases hxC : x ∈ C
    · exact (signedDist_nonpos_of_mem hxC).trans hs
    rw [signedDist_of_notMem hxC]
    have hρd : ρ < dist x c := by
      by_contra h
      exact hxC (hball (mem_closedBall.2 (le_of_not_gt h)))
    have hdpos : 0 < dist x c := lt_of_le_of_lt hρ hρd
    set p : E := c + (ρ / dist x c) • (x - c) with hp
    have hnorm : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
    have hpC : p ∈ C := by
      apply hball
      rw [mem_closedBall, hp, dist_eq_norm, add_sub_cancel_left, norm_smul, hnorm,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ hdpos.le), div_mul_cancel₀ _ hdpos.ne']
    have hxp : dist x p = dist x c - ρ := by
      have : x - p = (1 - ρ / dist x c) • (x - c) := by
        rw [hp, sub_smul, one_smul]; abel
      rw [dist_eq_norm, this, norm_smul, hnorm, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 ((div_le_one hdpos).2 hρd.le)), sub_mul, one_mul,
        div_mul_cancel₀ _ hdpos.ne']
    calc infDist x C ≤ dist x p := infDist_le_dist_of_mem hpC
      _ = dist x c - ρ := hxp
      _ ≤ s := by linarith

omit [NormedSpace ℝ E] in
/-- Conversely, every `s > signedDist C x` has a ball witness (for nonempty `C`). -/
theorem exists_closedBall_subset_of_signedDist_lt (hC : C.Nonempty) {s : ℝ}
    (hs : signedDist C x < s) :
    ∃ c : E, ∃ ρ : ℝ, 0 ≤ ρ ∧ closedBall c ρ ⊆ C ∧ dist x c ≤ ρ + s := by
  by_cases hxC : x ∈ C
  · rcases lt_or_ge s 0 with hs0 | hs0
    · refine ⟨x, -s, by linarith, fun q hq => ?_, by simp⟩
      rw [signedDist_of_mem hxC] at hs
      by_contra hqC
      have hq' : dist x q < infDist x Cᶜ := by
        rw [mem_closedBall, dist_comm] at hq; linarith
      exact notMem_of_dist_lt_infDist hq' hqC
    · refine ⟨x, 0, le_rfl, ?_, by simpa using hs0⟩
      rw [closedBall_zero]; exact singleton_subset_iff.2 hxC
  · rw [signedDist_of_notMem hxC] at hs
    obtain ⟨c, hc, hdc⟩ := (infDist_lt_iff hC).1 hs
    refine ⟨c, 0, le_rfl, ?_, by linarith⟩
    rw [closedBall_zero]; exact singleton_subset_iff.2 hc

/-- Convex combinations of balls inside a convex set stay inside it (any norm). -/
theorem closedBall_combo_subset (hC : Convex ℝ C) {c₁ c₂ : E} {ρ₁ ρ₂ : ℝ} (h₁ : 0 ≤ ρ₁)
    (h₂ : 0 ≤ ρ₂) (hb₁ : closedBall c₁ ρ₁ ⊆ C) (hb₂ : closedBall c₂ ρ₂ ⊆ C) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    closedBall (a • c₁ + b • c₂) (a * ρ₁ + b * ρ₂) ⊆ C := by
  intro q hq
  set R := a * ρ₁ + b * ρ₂ with hR
  set w := q - (a • c₁ + b • c₂) with hw
  have hwn : ‖w‖ ≤ R := by rw [hw, ← dist_eq_norm]; exact mem_closedBall.1 hq
  have hR0 : 0 ≤ R := by positivity
  rcases hR0.eq_or_lt with hR0 | hRpos
  · have : w = 0 := norm_le_zero_iff.1 (hR0 ▸ hwn)
    have hq' : q = a • c₁ + b • c₂ := by rw [← sub_eq_zero, ← hw, this]
    rw [hq']
    exact hC (hb₁ (mem_closedBall_self h₁)) (hb₂ (mem_closedBall_self h₂)) ha hb hab
  · have hm₁ : c₁ + (ρ₁ / R) • w ∈ C := by
      apply hb₁
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg h₁ hRpos.le)]
      calc ρ₁ / R * ‖w‖ ≤ ρ₁ / R * R := mul_le_mul_of_nonneg_left hwn (div_nonneg h₁ hRpos.le)
        _ = ρ₁ := div_mul_cancel₀ _ hRpos.ne'
    have hm₂ : c₂ + (ρ₂ / R) • w ∈ C := by
      apply hb₂
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg h₂ hRpos.le)]
      calc ρ₂ / R * ‖w‖ ≤ ρ₂ / R * R := mul_le_mul_of_nonneg_left hwn (div_nonneg h₂ hRpos.le)
        _ = ρ₂ := div_mul_cancel₀ _ hRpos.ne'
    have hcoef : a * (ρ₁ / R) + b * (ρ₂ / R) = 1 := by
      rw [mul_div_assoc', mul_div_assoc', ← add_div, ← hR, div_self hRpos.ne']
    have heq : a • (c₁ + (ρ₁ / R) • w) + b • (c₂ + (ρ₂ / R) • w) = q := by
      calc a • (c₁ + (ρ₁ / R) • w) + b • (c₂ + (ρ₂ / R) • w)
          = (a • c₁ + b • c₂) + (a * (ρ₁ / R) + b * (ρ₂ / R)) • w := by
            rw [smul_add, smul_add, smul_smul, smul_smul, add_smul]; abel
        _ = q := by rw [hcoef, one_smul, hw]; abel
    rw [← heq]
    exact hC hm₁ hm₂ ha hb hab

/-- **The signed distance to a convex set is convex** (any norm, `C` not necessarily closed). -/
theorem convexOn_signedDist (hC : Convex ℝ C) : ConvexOn ℝ univ (signedDist C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · rw [signedDist_empty]; exact convexOn_const 0 convex_univ
  rcases (Cᶜ).eq_empty_or_nonempty with hcu | hcne
  · rw [compl_empty_iff.1 hcu, signedDist_univ]; exact convexOn_const 0 convex_univ
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨c₁, ρ₁, h₁, hb₁, hd₁⟩ :=
    exists_closedBall_subset_of_signedDist_lt hne (lt_add_of_pos_right (signedDist C x) hε)
  obtain ⟨c₂, ρ₂, h₂, hb₂, hd₂⟩ :=
    exists_closedBall_subset_of_signedDist_lt hne (lt_add_of_pos_right (signedDist C y) hε)
  have hball := closedBall_combo_subset hC h₁ h₂ hb₁ hb₂ ha hb hab
  have hdist : dist (a • x + b • y) (a • c₁ + b • c₂) ≤
      (a * ρ₁ + b * ρ₂) + (a * (signedDist C x + ε) + b * (signedDist C y + ε)) := by
    calc dist (a • x + b • y) (a • c₁ + b • c₂)
        ≤ dist (a • x) (a • c₁) + dist (b • y) (b • c₂) := dist_add_add_le _ _ _ _
      _ = a * dist x c₁ + b * dist y c₂ := by
          rw [dist_smul₀, dist_smul₀, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * (ρ₁ + (signedDist C x + ε)) + b * (ρ₂ + (signedDist C y + ε)) :=
          add_le_add (mul_le_mul_of_nonneg_left hd₁ ha) (mul_le_mul_of_nonneg_left hd₂ hb)
      _ = _ := by ring
  have := signedDist_le_of_closedBall_subset hcne (by positivity) hball hdist
  have hε' : a * (signedDist C x + ε) + b * (signedDist C y + ε)
      = a * signedDist C x + b * signedDist C y + ε := by
    have : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
    linarith
  linarith

/-- Sublevel sets of the signed distance to a convex set are convex. -/
theorem convex_setOf_signedDist_le (hC : Convex ℝ C) (t : ℝ) :
    Convex ℝ {x | signedDist C x ≤ t} := by
  simpa using (convexOn_signedDist hC).convex_le t

/-! ## Sublevel sets -/

omit [NormedSpace ℝ E] in
theorem infDist_le_iff_mem_cthickening (hC : C.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    infDist x C ≤ t ↔ x ∈ cthickening t C := by
  rw [mem_cthickening_iff, ENNReal.le_ofReal_iff_toReal_le (infEdist_ne_top hC) ht]
  rfl

omit [NormedSpace ℝ E] in
/-- For `t ≥ 0`: `signedDist C x ≤ t ↔ x ∈ cthickening t C` (for nonempty `C`). -/
theorem signedDist_le_iff_mem_cthickening (hC : C.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    signedDist C x ≤ t ↔ x ∈ cthickening t C := by
  rw [← infDist_le_iff_mem_cthickening hC ht]
  by_cases hx : x ∈ C
  · rw [infDist_zero_of_mem hx]
    exact ⟨fun _ => ht, fun _ => (signedDist_nonpos_of_mem hx).trans ht⟩
  · rw [signedDist_of_notMem hx]

omit [NormedSpace ℝ E] in
theorem setOf_signedDist_le_of_nonneg (hC : C.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    {x | signedDist C x ≤ t} = cthickening t C := by
  ext x; exact signedDist_le_iff_mem_cthickening hC ht

/-- The inner parallel set is always contained in the sublevel set (any `C` with `Cᶜ ≠ ∅`, `t ≤ 0`). -/
theorem signedDist_le_of_closedBall_subset_self (hCc : Cᶜ.Nonempty) {t : ℝ} (ht : t ≤ 0)
    (h : closedBall x (-t) ⊆ C) : signedDist C x ≤ t :=
  signedDist_le_of_closedBall_subset hCc (by linarith) h (by simp)

omit [NormedSpace ℝ E] in
/-- A strict sublevel point has its closed ball inside `C` (any `C`, `t ≤ 0`). -/
theorem closedBall_subset_of_signedDist_lt {t : ℝ} (ht : t ≤ 0) (h : signedDist C x < t) :
    closedBall x (-t) ⊆ C := by
  have hxC : x ∈ C := by
    by_contra hx; have := signedDist_nonneg_of_notMem hx; linarith
  rw [signedDist_of_mem hxC] at h
  intro q hq
  by_contra hqC
  have hq' : dist x q < infDist x Cᶜ := by
    rw [mem_closedBall, dist_comm] at hq; linarith
  exact notMem_of_dist_lt_infDist hq' hqC

/-- For `t < 0` and closed `C`: `signedDist C x ≤ t ↔ closedBall x (-t) ⊆ C`. -/
theorem signedDist_le_iff_closedBall_subset (hCcl : IsClosed C) (hCc : Cᶜ.Nonempty) {t : ℝ}
    (ht : t < 0) : signedDist C x ≤ t ↔ closedBall x (-t) ⊆ C := by
  refine ⟨fun h => ?_, signedDist_le_of_closedBall_subset_self hCc ht.le⟩
  have hxC : x ∈ C := by
    by_contra hx; have := signedDist_nonneg_of_notMem hx; linarith
  rw [signedDist_of_mem hxC] at h
  have hball : ball x (-t) ⊆ C :=
    (ball_subset_ball (by linarith)).trans ball_infDist_compl_subset
  rw [← closure_ball x (by linarith : -t ≠ 0)]
  exact closure_minimal hball hCcl

theorem setOf_signedDist_le_of_neg (hCcl : IsClosed C) (hCc : Cᶜ.Nonempty) {t : ℝ} (ht : t < 0) :
    {x | signedDist C x ≤ t} = {x | closedBall x (-t) ⊆ C} := by
  ext x; exact signedDist_le_iff_closedBall_subset hCcl hCc ht

omit [NormedSpace ℝ E] in
/-- For `t ≥ 0`: `-t ≤ signedDist C x ↔ x ∈ cthickening t Cᶜ` (for `Cᶜ` nonempty). -/
theorem neg_le_signedDist_iff_mem_cthickening_compl (hCc : Cᶜ.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    -t ≤ signedDist C x ↔ x ∈ cthickening t Cᶜ := by
  rw [← signedDist_le_iff_mem_cthickening hCc ht, signedDist_compl]
  constructor <;> intro h <;> linarith

omit [NormedSpace ℝ E] in
/-- The `t`-shell: `|signedDist C x| ≤ t ↔ x ∈ cthickening t C ∩ cthickening t (interior C)ᶜ`, the
shell set of `TDInferenceConvexAll711.lean` (for `C`, `Cᶜ` nonempty, `t ≥ 0`). -/
theorem setOf_abs_signedDist_le (hC : C.Nonempty) (hCc : Cᶜ.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    {x | |signedDist C x| ≤ t} = cthickening t C ∩ cthickening t (interior C)ᶜ := by
  rw [← closure_compl, cthickening_closure]
  ext x
  simp only [mem_setOf_eq, mem_inter_iff, abs_le]
  rw [neg_le_signedDist_iff_mem_cthickening_compl hCc ht,
    signedDist_le_iff_mem_cthickening hC ht]
  exact and_comm

/-! ## Sign and topology -/

omit [NormedSpace ℝ E] in
/-- `signedDist C x ≤ 0 ↔ x ∈ closure C` (for nonempty `C`). -/
theorem signedDist_nonpos_iff (hC : C.Nonempty) : signedDist C x ≤ 0 ↔ x ∈ closure C := by
  constructor
  · intro h
    by_contra hx
    have hxC : x ∉ C := fun h' => hx (subset_closure h')
    rw [signedDist_of_notMem hxC] at h
    have := (infDist_pos_iff_notMem_closure hC).1 hx
    linarith
  · intro h
    have := signedDist_le_infDist C x
    rw [(mem_closure_iff_infDist_zero hC).1 h] at this
    exact this

omit [NormedSpace ℝ E] in
/-- `0 < signedDist C x ↔ x ∉ closure C` (for nonempty `C`). -/
theorem signedDist_pos_iff (hC : C.Nonempty) : 0 < signedDist C x ↔ x ∉ closure C := by
  rw [← signedDist_nonpos_iff hC, not_le]

omit [NormedSpace ℝ E] in
/-- `signedDist C x < 0 ↔ x ∈ interior C` (for `Cᶜ` nonempty). -/
theorem signedDist_neg_iff (hCc : Cᶜ.Nonempty) : signedDist C x < 0 ↔ x ∈ interior C := by
  have key := signedDist_pos_iff (C := Cᶜ) (x := x) hCc
  rw [signedDist_compl, closure_compl] at key
  simp only [mem_compl_iff, not_not] at key
  rw [← key]
  constructor <;> intro h <;> linarith

omit [NormedSpace ℝ E] in
/-- `signedDist C x = 0 ↔ x ∈ frontier C` (for `C` and `Cᶜ` nonempty). -/
theorem signedDist_eq_zero_iff (hC : C.Nonempty) (hCc : Cᶜ.Nonempty) :
    signedDist C x = 0 ↔ x ∈ frontier C := by
  rw [frontier, mem_diff, ← signedDist_nonpos_iff hC, ← signedDist_neg_iff hCc, not_lt]
  constructor
  · intro h; exact ⟨h.le, h.ge⟩
  · intro h; exact le_antisymm h.1 h.2

/-! ## Monotonicity in the set -/

omit [NormedSpace ℝ E] in
/-- Enlarging the set lowers the signed distance (for `C` nonempty and `Dᶜ` nonempty). -/
theorem signedDist_anti (hCD : C ⊆ D) (hC : C.Nonempty) (hDc : Dᶜ.Nonempty) (x : E) :
    signedDist D x ≤ signedDist C x := by
  have h1 : infDist x D ≤ infDist x C := infDist_le_infDist_of_subset hCD hC
  have h2 : infDist x Cᶜ ≤ infDist x Dᶜ :=
    infDist_le_infDist_of_subset (compl_subset_compl.2 hCD) hDc
  unfold signedDist; linarith

end StatisticalRL.Analysis.SignedDistance
