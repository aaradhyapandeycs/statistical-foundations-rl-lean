import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Formalization.Probability.GaussianAntiConcentration
import Formalization.Probability.StdGaussianPi

/-!
# Gaussian mass of convex shells

Infrastructure (not a source result) for the all-convex-sets route to `thm:Berry-Esseen-linear`
(`chapters/inference.tex:132–141`, with `d_cvx` at `:124–127`). Everything here is generic: it
concerns the standard Gaussian `stdGaussianPi ι` on `ι → ℝ` with the sup norm and its invertible
affine images; nothing is specific to the TD covariance.

For a set `K` and `r ≥ 0` the *`r`-shell* of `K` is
`cthickening r K ∩ cthickening r (interior K)ᶜ`: the points within `r` of `K` and within `r` of
the complement of its interior. With `S = card ι`:

* `stdGaussianPi_convexShell_le`: for convex `K`, the shell has standard Gaussian mass at most
  `4 S² r / √(2π)` (`stdGaussianPi_convexShell_le_ofReal` is the `ℝ≥0∞` form);
* `stdGaussianPi_frontier_convex_eq_zero`: convex frontiers are standard-Gaussian null;
* `map_affine_convexShell_le`: under `z ↦ c + L z` with `L` invertible the shell mass is at most
  `4 S² ‖L⁻¹‖ r / √(2π)`, where `‖L⁻¹‖ = matrixMaxRowAbsSum L⁻¹` is the `ℓ∞ → ℓ∞` operator norm
  (maximal absolute row sum);
* `map_affine_frontier_convex_eq_zero`, `map_affine_real_convex_eq_interior`,
  `map_affine_real_convex_eq_closure`: the image measure does not see convex frontiers, so the
  (outer) mass of a convex set, measurable or not, equals that of its interior and its closure;
  `stdGaussianPi_real_convex_eq_interior` and `stdGaussianPi_real_convex_eq_closure` are the
  untransformed forms.

Proof of the shell bound (paper proof: Steps 1–5 of the G1 check).
1. Every shell point `x` admits a nonzero `c` with `⟨c, z⟩ ≤ ⟨c, x⟩ + ‖c‖₁ r` on `K`
   (`exists_functional_of_mem_convexShell`): separate a nearest point `y ∉ interior K` from the
   open convex set `interior K` when it is nonempty, and otherwise take a functional vanishing on
   the direction of the proper affine span of `K`.
2. Normalizing, `‖u‖₁ ≤ 1` and some coordinate has `± S uᵢ ≥ 1`; this sorts the shell into the
   `2S` pieces `shellPiece K r i b`.
3. Each piece meets every line in direction `eᵢ` in a set of diameter at most `2 S r`.
4. Each piece is closed: it is the projection of a closed set along the compact set of admissible
   functionals.
5. Slicing (`measure_pi_le_of_slice_le`) and the density bound `1/√(2π)` give each piece mass at
   most `2 S r / √(2π)`.
-/

open MeasureTheory ProbabilityTheory Real Metric Set
open scoped ENNReal NNReal Matrix

namespace StatisticalRL.Probability

variable {ι : Type*} [Fintype ι]

/-! Proof-internal helpers live in the sub-namespace `GaussianConvexShell`. -/

namespace GaussianConvexShell

/-! ## Linear forms and the sup norm -/

/-- `|⟨u, w⟩| ≤ ‖u‖₁ ‖w‖∞`. -/
theorem abs_sum_mul_le_sum_abs_mul_norm (u w : ι → ℝ) :
    |∑ j, u j * w j| ≤ (∑ j, |u j|) * ‖w‖ := by
  calc |∑ j, u j * w j| ≤ ∑ j, |u j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |u j| * ‖w‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w j) (abs_nonneg _)
    _ = (∑ j, |u j|) * ‖w‖ := by rw [Finset.sum_mul]

theorem sum_mul_le_sum_mul_add (u x y : ι → ℝ) :
    ∑ j, u j * y j ≤ ∑ j, u j * x j + (∑ j, |u j|) * dist y x := by
  have h := abs_sum_mul_le_sum_abs_mul_norm u (y - x)
  have hsplit : ∑ j, u j * (y - x) j = ∑ j, u j * y j - ∑ j, u j * x j := by
    simp [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit] at h
  rw [dist_eq_norm]
  linarith [le_abs_self (∑ j, u j * y j - ∑ j, u j * x j)]

theorem continuous_sum_mul (u : ι → ℝ) : Continuous fun x : ι → ℝ ↦ ∑ j, u j * x j := by
  fun_prop

/-- A linear form on `ι → ℝ` is the dot product with its values on the standard basis. -/
theorem linearMap_apply_eq_sum [DecidableEq ι] (f : (ι → ℝ) →ₗ[ℝ] ℝ) (v : ι → ℝ) :
    f v = ∑ j, f (fun k ↦ if j = k then 1 else 0) * v j := by
  rw [LinearMap.pi_apply_eq_sum_univ f v]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul, mul_comm]

theorem linearMap_coeffs_ne_zero [DecidableEq ι] {f : (ι → ℝ) →ₗ[ℝ] ℝ} (hf : f ≠ 0) :
    (fun j ↦ f (fun k ↦ if j = k then 1 else 0)) ≠ 0 := by
  intro h
  apply hf
  refine LinearMap.ext fun v ↦ ?_
  rw [linearMap_apply_eq_sum]
  simp [show ∀ j, f (fun k ↦ if j = k then 1 else 0) = 0 from fun j ↦ congrFun h j]

/-! ## Step 1: a supporting functional at every shell point -/

/-- Every point `x` of the `r`-shell of a convex set `K` has a nonzero linear functional `c`
with `⟨c, z⟩ ≤ ⟨c, x⟩ + ‖c‖₁ r` for all `z ∈ K`. -/
theorem exists_functional_of_mem_convexShell {K : Set (ι → ℝ)} (hK : Convex ℝ K) {r : ℝ}
    (hr : 0 ≤ r) {x : ι → ℝ} (hx : x ∈ cthickening r K ∩ cthickening r (interior K)ᶜ) :
    ∃ c : ι → ℝ, c ≠ 0 ∧ ∀ z ∈ K, ∑ j, c j * z j ≤ ∑ j, c j * x j + (∑ j, |c j|) * r := by
  classical
  obtain ⟨hxK, hxI⟩ := hx
  by_cases hint : (interior K).Nonempty
  · -- separate a nearest point of `(interior K)ᶜ` from `interior K`
    rw [cthickening_eq_biUnion_closedBall _ hr, isOpen_interior.isClosed_compl.closure_eq]
      at hxI
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hxI
    rw [mem_closedBall] at hxy
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hy
    let g : (ι → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap
    have hg : ∀ v, f v = g v := fun v ↦ rfl
    have hfK : ∀ z ∈ K, f z ≤ f y := by
      have hsub : closure (interior K) ⊆ {a | f a ≤ f y} :=
        closure_minimal (fun a ha ↦ (hf a ha).le) (isClosed_le f.continuous continuous_const)
      rw [hK.closure_interior_eq_closure_of_nonempty_interior hint] at hsub
      exact fun z hz ↦ hsub (subset_closure hz)
    have hg0 : g ≠ 0 := by
      intro h0
      obtain ⟨a, ha⟩ := hint
      have := hf a ha
      rw [hg, hg, h0] at this
      simp at this
    refine ⟨_, linearMap_coeffs_ne_zero hg0, fun z hz ↦ ?_⟩
    beta_reduce
    have h1 := hfK z hz
    rw [hg, hg, linearMap_apply_eq_sum g z, linearMap_apply_eq_sum g y] at h1
    have h2 := sum_mul_le_sum_mul_add (fun j ↦ g (fun k ↦ if j = k then 1 else 0)) x y
    have h3 : (∑ j, |g (fun k ↦ if j = k then 1 else 0)|) * dist y x ≤
        (∑ j, |g (fun k ↦ if j = k then 1 else 0)|) * r :=
      mul_le_mul_of_nonneg_left (by rwa [dist_comm]) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    linarith
  · -- empty interior: a functional constant on `K`
    have hKne : K.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hxK
    obtain ⟨z₀, hz₀⟩ := hKne
    have hspan : affineSpan ℝ K ≠ ⊤ := by
      rwa [Ne, ← hK.interior_nonempty_iff_affineSpan_eq_top]
    have hdir : (affineSpan ℝ K).direction ≠ ⊤ := by
      rwa [Ne, AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨z₀, subset_affineSpan ℝ K hz₀⟩]
    obtain ⟨g, hg0, hgker⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hdir)
    have hconst : ∀ z ∈ K, g z = g z₀ := by
      intro z hz
      have hmem : z -ᵥ z₀ ∈ (affineSpan ℝ K).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hz)
          (subset_affineSpan ℝ K hz₀)
      have := hgker hmem
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
      exact this
    have hgc : Continuous g := LinearMap.continuous_of_finiteDimensional g
    have hconstcl : ∀ w ∈ closure K, g w = g z₀ := by
      have hsub : closure K ⊆ {a | g a = g z₀} :=
        closure_minimal hconst (isClosed_eq hgc continuous_const)
      exact fun w hw ↦ hsub hw
    rw [cthickening_eq_biUnion_closedBall _ hr] at hxK
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.1 hxK
    rw [mem_closedBall] at hxw
    refine ⟨_, linearMap_coeffs_ne_zero hg0, fun z hz ↦ ?_⟩
    beta_reduce
    have h1 : g z = g w := (hconst z hz).trans (hconstcl w hw).symm
    rw [linearMap_apply_eq_sum g z, linearMap_apply_eq_sum g w] at h1
    have h2 := sum_mul_le_sum_mul_add (fun j ↦ g (fun k ↦ if j = k then 1 else 0)) x w
    have h3 : (∑ j, |g (fun k ↦ if j = k then 1 else 0)|) * dist w x ≤
        (∑ j, |g (fun k ↦ if j = k then 1 else 0)|) * r :=
      mul_le_mul_of_nonneg_left (by rwa [dist_comm]) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    linarith

/-! ## Step 2: the `2S` pieces -/

/-- The sign `+1` (`true`) or `-1` (`false`). -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> simp [boolSign]

/-- Admissible normals for the piece `(i, b)`: `‖u‖₁ ≤ 1` and `S · (±uᵢ) ≥ 1`. -/
def shellPieceDirs (i : ι) (b : Bool) : Set (ι → ℝ) :=
  {u | ∑ j, |u j| ≤ 1 ∧ 1 ≤ (Fintype.card ι : ℝ) * (boolSign b * u i)}

/-- The piece `(i, b)` of the `r`-shell of `K`: points of `cthickening r K` with an admissible
normal `u` for `(i, b)` satisfying `⟨u, z⟩ ≤ ⟨u, p⟩ + r` on `K`. -/
def shellPiece (K : Set (ι → ℝ)) (r : ℝ) (i : ι) (b : Bool) : Set (ι → ℝ) :=
  cthickening r K ∩
    {p | ∃ u ∈ shellPieceDirs i b, ∀ z ∈ K, ∑ j, u j * z j ≤ ∑ j, u j * p j + r}

theorem shellPiece_subset_cthickening {K : Set (ι → ℝ)} {r : ℝ} {i : ι} {b : Bool} :
    shellPiece K r i b ⊆ cthickening r K :=
  inter_subset_left

/-- Step 2: the shell of a convex set is covered by the pieces. -/
theorem convexShell_subset_iUnion_shellPiece {K : Set (ι → ℝ)} (hK : Convex ℝ K) {r : ℝ}
    (hr : 0 ≤ r) :
    cthickening r K ∩ cthickening r (interior K)ᶜ ⊆ ⋃ p : ι × Bool, shellPiece K r p.1 p.2 := by
  intro x hx
  obtain ⟨c, hc0, hc⟩ := exists_functional_of_mem_convexShell hK hr hx
  set L := ∑ j, |c j| with hLdef
  have hLpos : 0 < L := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc0
    exact lt_of_lt_of_le (abs_pos.2 hj)
      (Finset.single_le_sum (f := fun j ↦ |c j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨j, -⟩ := Function.ne_iff.1 hc0
    exact ⟨j, Finset.mem_univ j⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ |c j|) hne
  let u : ι → ℝ := fun j ↦ c j / L
  have hsumu : ∑ j, |u j| = 1 := by
    simp only [u, abs_div, abs_of_pos hLpos, ← Finset.sum_div, ← hLdef]
    exact div_self hLpos.ne'
  have hLle : L ≤ (Fintype.card ι : ℝ) * |c i| := by
    calc L = ∑ j, |c j| := rfl
      _ ≤ ∑ _j : ι, |c i| := Finset.sum_le_sum fun j _ ↦ hi j (Finset.mem_univ j)
      _ = (Fintype.card ι : ℝ) * |c i| := by simp
  refine mem_iUnion.2 ⟨(i, decide (0 ≤ c i)), hx.1, u, ⟨hsumu.le, ?_⟩, fun z hz ↦ ?_⟩
  · have habs : boolSign (decide (0 ≤ c i)) * c i = |c i| := by
      by_cases h : 0 ≤ c i
      · simp [boolSign, h, abs_of_nonneg h]
      · simp [boolSign, h, abs_of_neg (lt_of_not_ge h)]
    simp only [u]
    rw [mul_div_assoc', habs, ← mul_div_assoc, le_div_iff₀ hLpos, one_mul]
    exact hLle
  · have h := hc z hz
    simp only [u, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_le_iff₀ hLpos, add_mul, div_mul_cancel₀ _ hLpos.ne']
    linarith [mul_comm r L]

/-! ## Step 3: thin line sections -/

/-- Step 3: along direction `eᵢ`, a piece `(i, b)` has sections of diameter at most `2 S r`. -/
theorem abs_sub_le_of_update_mem_shellPiece [DecidableEq ι] {K : Set (ι → ℝ)} {r : ℝ}
    (hr : 0 ≤ r) {i : ι} {b : Bool} (x : ι → ℝ) {y y' : ℝ}
    (hy : Function.update x i y ∈ shellPiece K r i b)
    (hy' : Function.update x i y' ∈ shellPiece K r i b) :
    |y' - y| ≤ 2 * (Fintype.card ι : ℝ) * r := by
  -- one-sided bound: `σ (y' - y) ≤ 2 S r` using the normal at `update x i y`
  have key : ∀ {y y' : ℝ}, Function.update x i y ∈ shellPiece K r i b →
      Function.update x i y' ∈ cthickening r K →
      boolSign b * (y' - y) ≤ 2 * (Fintype.card ι : ℝ) * r := by
    intro y y' hy hy'
    obtain ⟨-, u, ⟨hu1, hui⟩, hu⟩ := hy
    have hcl : ∀ z ∈ closure K, ∑ j, u j * z j ≤ ∑ j, u j * Function.update x i y j + r := by
      have hsub : closure K ⊆ {z | ∑ j, u j * z j ≤ ∑ j, u j * Function.update x i y j + r} :=
        closure_minimal hu (isClosed_le (continuous_sum_mul u) continuous_const)
      exact fun z hz ↦ hsub hz
    rw [cthickening_eq_biUnion_closedBall _ hr] at hy'
    obtain ⟨w, hw, hqw⟩ := mem_iUnion₂.1 hy'
    rw [mem_closedBall] at hqw
    have h1 := sum_mul_le_sum_mul_add u w (Function.update x i y')
    have h2 : (∑ j, |u j|) * dist (Function.update x i y') w ≤ r := by
      calc (∑ j, |u j|) * dist (Function.update x i y') w ≤ 1 * r :=
            mul_le_mul hu1 hqw dist_nonneg zero_le_one
        _ = r := one_mul r
    have h3 := hcl w hw
    have hpq : ∑ j, u j * Function.update x i y' j =
        ∑ j, u j * Function.update x i y j + u i * (y' - y) := by
      rw [sum_mul_update_eq, sum_mul_update_eq]
      ring
    have hS : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have hσ := boolSign_mul_self b
    -- `u i (y' - y) ≤ 2 r`
    have hlin : u i * (y' - y) ≤ 2 * r := by linarith
    by_cases hneg : boolSign b * (y' - y) ≤ 0
    · have := mul_nonneg hS hr
      linarith
    · push_neg at hneg
      have : u i * (y' - y) = (boolSign b * u i) * (boolSign b * (y' - y)) := by
        linear_combination (u i * (y' - y)) * hσ.symm
      calc boolSign b * (y' - y)
          ≤ ((Fintype.card ι : ℝ) * (boolSign b * u i)) * (boolSign b * (y' - y)) :=
            le_mul_of_one_le_left hneg.le hui
        _ = (Fintype.card ι : ℝ) * (u i * (y' - y)) := by rw [this]; ring
        _ ≤ (Fintype.card ι : ℝ) * (2 * r) := mul_le_mul_of_nonneg_left hlin hS
        _ = 2 * (Fintype.card ι : ℝ) * r := by ring
  have h1 := key hy (shellPiece_subset_cthickening hy')
  have h2 := key hy' (shellPiece_subset_cthickening hy)
  rw [abs_le]
  cases b <;> simp [boolSign] at h1 h2 <;> constructor <;> linarith

/-! ## Step 4: the pieces are closed -/

theorem isCompact_shellPieceDirs (i : ι) (b : Bool) : IsCompact (shellPieceDirs (ι := ι) i b) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le (continuous_finset_sum _ fun j _ ↦ (continuous_apply j).abs)
      continuous_const).inter
      (isClosed_le continuous_const (continuous_const.mul (continuous_const.mul
        (continuous_apply i))))
  · refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset fun u hu ↦ ?_
    rw [mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ ?_
    rw [Real.norm_eq_abs]
    exact le_trans (Finset.single_le_sum (f := fun j ↦ |u j|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ j)) hu.1

theorem isClosed_shellPiece (K : Set (ι → ℝ)) (r : ℝ) (i : ι) (b : Bool) :
    IsClosed (shellPiece K r i b) := by
  refine isClosed_cthickening.inter ?_
  haveI : CompactSpace (shellPieceDirs (ι := ι) i b) :=
    isCompact_iff_compactSpace.1 (isCompact_shellPieceDirs i b)
  let F : Set ((ι → ℝ) × shellPieceDirs (ι := ι) i b) :=
    {q | ∀ z ∈ K, ∑ j, (q.2 : ι → ℝ) j * z j ≤ ∑ j, (q.2 : ι → ℝ) j * q.1 j + r}
  have hF : IsClosed F := by
    simp only [F, setOf_forall]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦ isClosed_le ?_ ?_
    · exact continuous_finset_sum _ fun j _ ↦
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)).mul
          continuous_const
    · exact (continuous_finset_sum _ fun j _ ↦
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)).mul
          ((continuous_apply j).comp continuous_fst)).add continuous_const
  have heq : {p | ∃ u ∈ shellPieceDirs i b, ∀ z ∈ K, ∑ j, u j * z j ≤ ∑ j, u j * p j + r} =
      Prod.fst '' F := by
    ext p
    constructor
    · rintro ⟨u, hu, h⟩
      exact ⟨(p, ⟨u, hu⟩), h, rfl⟩
    · rintro ⟨⟨p', u, hu⟩, h, rfl⟩
      exact ⟨u, hu, h⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace F hF

/-! ## Step 5: slicing -/

/-- A set of reals whose points are pairwise within `d` has `N(0,1)`-mass at most `d/√(2π)`. -/
theorem gaussianReal_le_of_abs_sub_le {A : Set ℝ} {d : ℝ}
    (h : ∀ y ∈ A, ∀ y' ∈ A, |y' - y| ≤ d) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (d / √(2 * π)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp
  have hbdd : BddBelow A := ⟨y₀ - d, fun y hy ↦ by
    have := h y₀ hy₀ y hy
    linarith [neg_abs_le (y - y₀)]⟩
  have hsub : A ⊆ Icc (sInf A) (sInf A + d) := by
    intro y hy
    refine ⟨csInf_le hbdd hy, ?_⟩
    have : y - d ≤ sInf A := le_csInf ⟨y₀, hy₀⟩ fun y' hy' ↦ by
      have := h y' hy' y hy
      linarith [le_abs_self (y - y')]
    linarith
  refine (measure_mono hsub).trans ((gaussianReal_Icc_le 0 one_ne_zero _ _).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  simp only [NNReal.coe_one, mul_one, add_sub_cancel_left]
  rw [div_eq_inv_mul]

theorem stdGaussianPi_shellPiece_le [DecidableEq ι] (K : Set (ι → ℝ)) {r : ℝ} (hr : 0 ≤ r)
    (i : ι) (b : Bool) :
    stdGaussianPi ι (shellPiece K r i b) ≤
      ENNReal.ofReal (2 * (Fintype.card ι : ℝ) * r / √(2 * π)) := by
  refine measure_pi_le_of_slice_le _ (isClosed_shellPiece K r i b).measurableSet i fun x ↦ ?_
  exact gaussianReal_le_of_abs_sub_le fun y hy y' hy' ↦
    abs_sub_le_of_update_mem_shellPiece hr x hy hy'

end GaussianConvexShell

open GaussianConvexShell

/-! ## The shell bound -/

/-- **Gaussian convex shell bound** (infrastructure, not a source result). For convex `K ⊆ ℝ^ι`
(sup norm) and `r ≥ 0`, the standard Gaussian mass of the `r`-shell
`cthickening r K ∩ cthickening r (interior K)ᶜ` is at most `4 S² r / √(2π)`, `S = card ι`. -/
theorem stdGaussianPi_convexShell_le_ofReal {K : Set (ι → ℝ)} (hK : Convex ℝ K) {r : ℝ}
    (hr : 0 ≤ r) :
    stdGaussianPi ι (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      ENNReal.ofReal (4 * (Fintype.card ι : ℝ) ^ 2 * r / √(2 * π)) := by
  classical
  calc stdGaussianPi ι (cthickening r K ∩ cthickening r (interior K)ᶜ)
      ≤ stdGaussianPi ι (⋃ p : ι × Bool, shellPiece K r p.1 p.2) :=
        measure_mono (convexShell_subset_iUnion_shellPiece hK hr)
    _ ≤ ∑ p : ι × Bool, stdGaussianPi ι (shellPiece K r p.1 p.2) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : ι × Bool, ENNReal.ofReal (2 * (Fintype.card ι : ℝ) * r / √(2 * π)) :=
        Finset.sum_le_sum fun p _ ↦ stdGaussianPi_shellPiece_le K hr p.1 p.2
    _ = ENNReal.ofReal (4 * (Fintype.card ι : ℝ) ^ 2 * r / √(2 * π)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        ring

/-- **Gaussian convex shell bound**, real form (infrastructure, not a source result):
`P(Z ∈ cthickening r K ∩ cthickening r (interior K)ᶜ) ≤ 4 S² r / √(2π)` for `Z` standard
Gaussian on `ι → ℝ` (sup norm), `K` convex, `r ≥ 0`, `S = card ι`. -/
theorem stdGaussianPi_convexShell_le {K : Set (ι → ℝ)} (hK : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r) :
    (stdGaussianPi ι).real (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      4 * (Fintype.card ι : ℝ) ^ 2 * r / √(2 * π) :=
  ENNReal.toReal_le_of_le_ofReal (div_nonneg (mul_nonneg (by positivity) hr) (Real.sqrt_nonneg _))
    (stdGaussianPi_convexShell_le_ofReal hK hr)

theorem frontier_subset_convexShell (K : Set (ι → ℝ)) (r : ℝ) :
    frontier K ⊆ cthickening r K ∩ cthickening r (interior K)ᶜ := by
  intro x hx
  exact ⟨closure_subset_cthickening r K hx.1,
    self_subset_cthickening _ (show x ∉ interior K from hx.2)⟩

/-- The frontier of a convex set is null for the standard Gaussian (infrastructure). -/
theorem stdGaussianPi_frontier_convex_eq_zero {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    stdGaussianPi ι (frontier K) = 0 := by
  have hle : ∀ r : ℝ, 0 < r →
      (stdGaussianPi ι).real (frontier K) ≤ 4 * (Fintype.card ι : ℝ) ^ 2 / √(2 * π) * r := by
    intro r hr
    calc (stdGaussianPi ι).real (frontier K)
        ≤ (stdGaussianPi ι).real (cthickening r K ∩ cthickening r (interior K)ᶜ) :=
          measureReal_mono (frontier_subset_convexShell K r)
      _ ≤ 4 * (Fintype.card ι : ℝ) ^ 2 * r / √(2 * π) := stdGaussianPi_convexShell_le hK hr.le
      _ = 4 * (Fintype.card ι : ℝ) ^ 2 / √(2 * π) * r := by ring
  have h0 : (stdGaussianPi ι).real (frontier K) ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    set C := 4 * (Fintype.card ι : ℝ) ^ 2 / √(2 * π)
    have hC : 0 ≤ C := by positivity
    have := hle ((stdGaussianPi ι).real (frontier K) / (2 * (C + 1)))
      (div_pos hpos (by linarith))
    have hC1 : C * ((stdGaussianPi ι).real (frontier K) / (2 * (C + 1))) <
        (stdGaussianPi ι).real (frontier K) := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  exact (measureReal_eq_zero_iff).1 (le_antisymm h0 measureReal_nonneg)

/-! ## Frontier-null measures -/

omit [Fintype ι] in
theorem measure_eq_interior_of_frontier_null {μ : Measure (ι → ℝ)} {K : Set (ι → ℝ)}
    (h : μ (frontier K) = 0) : μ K = μ (interior K) := by
  refine le_antisymm ?_ (measure_mono interior_subset)
  calc μ K ≤ μ (closure K) := measure_mono subset_closure
    _ = μ (interior K ∪ frontier K) := by rw [closure_eq_interior_union_frontier]
    _ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _
    _ = μ (interior K) := by rw [h, add_zero]

omit [Fintype ι] in
theorem measure_closure_eq_interior_of_frontier_null {μ : Measure (ι → ℝ)} {K : Set (ι → ℝ)}
    (h : μ (frontier K) = 0) : μ (closure K) = μ (interior K) := by
  refine le_antisymm ?_ (measure_mono (interior_subset.trans subset_closure))
  calc μ (closure K) = μ (interior K ∪ frontier K) := by rw [closure_eq_interior_union_frontier]
    _ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _
    _ = μ (interior K) := by rw [h, add_zero]

/-- The standard Gaussian mass of a convex set equals that of its interior (infrastructure). -/
theorem stdGaussianPi_real_convex_eq_interior {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    (stdGaussianPi ι).real K = (stdGaussianPi ι).real (interior K) := by
  simp only [measureReal_def]
  rw [measure_eq_interior_of_frontier_null (stdGaussianPi_frontier_convex_eq_zero hK)]

/-- The standard Gaussian mass of a convex set equals that of its closure (infrastructure). -/
theorem stdGaussianPi_real_convex_eq_closure {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    (stdGaussianPi ι).real K = (stdGaussianPi ι).real (closure K) := by
  rw [stdGaussianPi_real_convex_eq_interior hK, measureReal_def, measureReal_def,
    measure_closure_eq_interior_of_frontier_null (stdGaussianPi_frontier_convex_eq_zero hK)]

/-! ## Invertible affine images -/

/-- The maximal absolute row sum `maxᵢ ∑ⱼ |Aᵢⱼ|` of a square matrix: its `ℓ∞ → ℓ∞` operator
norm (the value of Mathlib's `Matrix.linfty_opNorm_def`). -/
noncomputable def matrixMaxRowAbsSum (A : Matrix ι ι ℝ) : ℝ :=
  ((Finset.univ.sup fun i ↦ ∑ j, ‖A i j‖₊ : ℝ≥0) : ℝ)

open scoped Matrix.Norms.Operator in
/-- `matrixMaxRowAbsSum` is Mathlib's `ℓ∞` operator norm (`Matrix.Norms.Operator`). -/
theorem matrixMaxRowAbsSum_eq_linfty_opNorm (A : Matrix ι ι ℝ) : matrixMaxRowAbsSum A = ‖A‖ :=
  (Matrix.linfty_opNorm_def A).symm

theorem matrixMaxRowAbsSum_nonneg (A : Matrix ι ι ℝ) : 0 ≤ matrixMaxRowAbsSum A :=
  NNReal.coe_nonneg _

theorem sum_abs_le_matrixMaxRowAbsSum (A : Matrix ι ι ℝ) (i : ι) :
    ∑ j, |A i j| ≤ matrixMaxRowAbsSum A := by
  have h : (∑ j, ‖A i j‖₊) ≤ Finset.univ.sup fun i ↦ ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i ↦ ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.2 h
  simpa [matrixMaxRowAbsSum, NNReal.coe_sum, Real.norm_eq_abs] using h'

theorem norm_mulVec_le_matrixMaxRowAbsSum (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    ‖A *ᵥ v‖ ≤ matrixMaxRowAbsSum A * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (matrixMaxRowAbsSum_nonneg A) (norm_nonneg v))).2 fun i ↦ ?_
  rw [Real.norm_eq_abs]
  calc |(A *ᵥ v) i| = |∑ j, A i j * v j| := by simp only [Matrix.mulVec, dotProduct]
    _ ≤ (∑ j, |A i j|) * ‖v‖ := abs_sum_mul_le_sum_abs_mul_norm _ _
    _ ≤ matrixMaxRowAbsSum A * ‖v‖ :=
        mul_le_mul_of_nonneg_right (sum_abs_le_matrixMaxRowAbsSum A i) (norm_nonneg v)

namespace GaussianConvexShell

/-- The affine homeomorphism `z ↦ c + L z` of `ι → ℝ` for an invertible matrix `L`. -/
noncomputable def affineHomeomorph [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : IsUnit L.det)
    (c : ι → ℝ) : (ι → ℝ) ≃ₜ (ι → ℝ) where
  toFun z := c + L *ᵥ z
  invFun w := L⁻¹ *ᵥ (w - c)
  left_inv z := by
    simp only [add_sub_cancel_left, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hL,
      Matrix.one_mulVec]
  right_inv w := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hL, Matrix.one_mulVec,
      add_sub_cancel]
  continuous_toFun := continuous_const.add (continuous_const.matrix_mulVec continuous_id)
  continuous_invFun :=
    continuous_const.matrix_mulVec (continuous_id.sub continuous_const)

section Affine

variable [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : IsUnit L.det) (c : ι → ℝ)
include hL

theorem affineHomeomorph_apply (z : ι → ℝ) : affineHomeomorph L hL c z = c + L *ᵥ z := rfl

theorem affineHomeomorph_symm_apply (w : ι → ℝ) :
    (affineHomeomorph L hL c).symm w = L⁻¹ *ᵥ (w - c) := rfl

/-- Pulling back a closed thickening along `z ↦ c + L z` costs the factor `‖L⁻¹‖`. -/
theorem preimage_cthickening_subset_affine {A : Set (ι → ℝ)} {r : ℝ} (hr : 0 ≤ r) :
    (fun z ↦ c + L *ᵥ z) ⁻¹' cthickening r A ⊆
      cthickening (matrixMaxRowAbsSum L⁻¹ * r) ((fun z ↦ c + L *ᵥ z) ⁻¹' A) := by
  intro z hz
  rw [mem_preimage, cthickening_eq_biUnion_closedBall _ hr] at hz
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.1 hz
  rw [mem_closedBall] at hzw
  rw [← cthickening_closure]
  refine mem_cthickening_of_dist_le z ((affineHomeomorph L hL c).symm w) _ _ ?_ ?_
  · show (affineHomeomorph L hL c).symm w ∈ closure (affineHomeomorph L hL c ⁻¹' A)
    rw [← (affineHomeomorph L hL c).preimage_closure, mem_preimage,
      (affineHomeomorph L hL c).apply_symm_apply]
    exact hw
  · have hdiff : z - (affineHomeomorph L hL c).symm w = L⁻¹ *ᵥ ((c + L *ᵥ z) - w) := by
      rw [affineHomeomorph_symm_apply]
      conv_lhs => rw [← (affineHomeomorph L hL c).symm_apply_apply z]
      rw [affineHomeomorph_symm_apply, affineHomeomorph_apply, ← Matrix.mulVec_sub]
      congr 1
      abel
    rw [dist_eq_norm, hdiff]
    calc ‖L⁻¹ *ᵥ ((c + L *ᵥ z) - w)‖ ≤ matrixMaxRowAbsSum L⁻¹ * ‖(c + L *ᵥ z) - w‖ :=
          norm_mulVec_le_matrixMaxRowAbsSum _ _
      _ ≤ matrixMaxRowAbsSum L⁻¹ * r :=
          mul_le_mul_of_nonneg_left (by rwa [← dist_eq_norm]) (matrixMaxRowAbsSum_nonneg _)

/-- The pullback of the `r`-shell of `K` along `z ↦ c + L z` lies in the `‖L⁻¹‖ r`-shell of the
pulled-back set. -/
theorem preimage_convexShell_subset_affine (K : Set (ι → ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    (fun z ↦ c + L *ᵥ z) ⁻¹' (cthickening r K ∩ cthickening r (interior K)ᶜ) ⊆
      cthickening (matrixMaxRowAbsSum L⁻¹ * r) ((fun z ↦ c + L *ᵥ z) ⁻¹' K) ∩
        cthickening (matrixMaxRowAbsSum L⁻¹ * r) (interior ((fun z ↦ c + L *ᵥ z) ⁻¹' K))ᶜ := by
  rintro z ⟨h1, h2⟩
  refine ⟨preimage_cthickening_subset_affine L hL c hr h1, ?_⟩
  have h3 := preimage_cthickening_subset_affine L hL c hr h2
  have heq : (fun z ↦ c + L *ᵥ z) ⁻¹' (interior K)ᶜ =
      (interior ((fun z ↦ c + L *ᵥ z) ⁻¹' K))ᶜ := by
    rw [preimage_compl]
    congr 1
    exact (affineHomeomorph L hL c).preimage_interior K
  rwa [heq] at h3

omit [DecidableEq ι] hL in
theorem convex_preimage_affine {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    Convex ℝ ((fun z ↦ c + L *ᵥ z) ⁻¹' K) :=
  (hK.translate_preimage_right c).linear_preimage (Matrix.mulVecLin L)

theorem measurable_affine : Measurable fun z : ι → ℝ ↦ c + L *ᵥ z :=
  (affineHomeomorph L hL c).continuous.measurable

end Affine

end GaussianConvexShell

open GaussianConvexShell

section AffineMain

variable [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : IsUnit L.det) (c : ι → ℝ)
include hL

/-- For an invertible affine `f z = c + L z`, the pushforward of any measure evaluates on every
set, measurable or not, as the measure of the preimage. -/
theorem map_affine_measure_apply (μ : Measure (ι → ℝ)) (s : Set (ι → ℝ)) :
    μ.map (fun z ↦ c + L *ᵥ z) s = μ ((fun z ↦ c + L *ᵥ z) ⁻¹' s) :=
  (affineHomeomorph L hL c).toMeasurableEquiv.map_apply s

/-- `.real` form of `map_affine_measure_apply`. -/
theorem map_affine_measureReal_apply (μ : Measure (ι → ℝ)) (s : Set (ι → ℝ)) :
    (μ.map (fun z ↦ c + L *ᵥ z)).real s = μ.real ((fun z ↦ c + L *ᵥ z) ⁻¹' s) := by
  simp only [measureReal_def, map_affine_measure_apply L hL c μ s]

/-- **Gaussian convex shell bound for invertible affine images** (infrastructure, not a source
result). If `Z` is standard Gaussian on `ι → ℝ` (sup norm), `L` is invertible and `K` is convex,
then `P(c + L Z ∈ cthickening r K ∩ cthickening r (interior K)ᶜ) ≤ 4 S² ‖L⁻¹‖ r / √(2π)`, where
`‖L⁻¹‖ = matrixMaxRowAbsSum L⁻¹` is the maximal absolute row sum and `S = card ι`. -/
theorem map_affine_convexShell_le {K : Set (ι → ℝ)} (hK : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r) :
    ((stdGaussianPi ι).map (fun z ↦ c + L *ᵥ z)).real
        (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum L⁻¹ * r / √(2 * π) := by
  have hmeas : MeasurableSet (cthickening r K ∩ cthickening r (interior K)ᶜ) :=
    (isClosed_cthickening.inter isClosed_cthickening).measurableSet
  rw [map_measureReal_apply (measurable_affine L hL c) hmeas]
  calc (stdGaussianPi ι).real
        ((fun z ↦ c + L *ᵥ z) ⁻¹' (cthickening r K ∩ cthickening r (interior K)ᶜ))
      ≤ (stdGaussianPi ι).real
          (cthickening (matrixMaxRowAbsSum L⁻¹ * r) ((fun z ↦ c + L *ᵥ z) ⁻¹' K) ∩
            cthickening (matrixMaxRowAbsSum L⁻¹ * r)
              (interior ((fun z ↦ c + L *ᵥ z) ⁻¹' K))ᶜ) :=
        measureReal_mono (preimage_convexShell_subset_affine L hL c K hr)
    _ ≤ 4 * (Fintype.card ι : ℝ) ^ 2 * (matrixMaxRowAbsSum L⁻¹ * r) / √(2 * π) :=
        stdGaussianPi_convexShell_le (convex_preimage_affine L c hK)
          (mul_nonneg (matrixMaxRowAbsSum_nonneg _) hr)
    _ = 4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum L⁻¹ * r / √(2 * π) := by ring

/-- Convex frontiers are null for every invertible affine image of the standard Gaussian
(infrastructure). -/
theorem map_affine_frontier_convex_eq_zero {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    (stdGaussianPi ι).map (fun z ↦ c + L *ᵥ z) (frontier K) = 0 := by
  rw [Measure.map_apply (measurable_affine L hL c) isClosed_frontier.measurableSet]
  have h : (fun z ↦ c + L *ᵥ z) ⁻¹' frontier K = frontier ((fun z ↦ c + L *ᵥ z) ⁻¹' K) :=
    (affineHomeomorph L hL c).preimage_frontier K
  rw [h]
  exact stdGaussianPi_frontier_convex_eq_zero (convex_preimage_affine L c hK)

/-- For an invertible affine image of the standard Gaussian, the (outer) mass of a convex set,
measurable or not, equals the mass of its interior (infrastructure). -/
theorem map_affine_real_convex_eq_interior {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    ((stdGaussianPi ι).map (fun z ↦ c + L *ᵥ z)).real K =
      ((stdGaussianPi ι).map (fun z ↦ c + L *ᵥ z)).real (interior K) := by
  simp only [measureReal_def]
  rw [measure_eq_interior_of_frontier_null (map_affine_frontier_convex_eq_zero L hL c hK)]

/-- For an invertible affine image of the standard Gaussian, the (outer) mass of a convex set,
measurable or not, equals the mass of its closure (infrastructure). -/
theorem map_affine_real_convex_eq_closure {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    ((stdGaussianPi ι).map (fun z ↦ c + L *ᵥ z)).real K =
      ((stdGaussianPi ι).map (fun z ↦ c + L *ᵥ z)).real (closure K) := by
  rw [map_affine_real_convex_eq_interior L hL c hK, measureReal_def, measureReal_def,
    measure_closure_eq_interior_of_frontier_null (map_affine_frontier_convex_eq_zero L hL c hK)]

end AffineMain

/-! ## Linear images (`c = 0`) -/

section Linear

variable [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : IsUnit L.det)
include hL

omit [DecidableEq ι] hL in
theorem map_mulVec_eq_map_affine_zero (μ : Measure (ι → ℝ)) :
    μ.map (fun z ↦ L *ᵥ z) = μ.map (fun z ↦ (0 : ι → ℝ) + L *ᵥ z) := by
  simp only [zero_add]

/-- `map_affine_convexShell_le` with `c = 0` (infrastructure). -/
theorem map_mulVec_convexShell_le {K : Set (ι → ℝ)} (hK : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r) :
    ((stdGaussianPi ι).map (fun z ↦ L *ᵥ z)).real
        (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum L⁻¹ * r / √(2 * π) := by
  rw [map_mulVec_eq_map_affine_zero L]
  exact map_affine_convexShell_le L hL 0 hK hr

/-- `map_affine_frontier_convex_eq_zero` with `c = 0` (infrastructure). -/
theorem map_mulVec_frontier_convex_eq_zero {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    (stdGaussianPi ι).map (fun z ↦ L *ᵥ z) (frontier K) = 0 := by
  rw [map_mulVec_eq_map_affine_zero L]
  exact map_affine_frontier_convex_eq_zero L hL 0 hK

/-- `map_affine_real_convex_eq_interior` with `c = 0` (infrastructure). -/
theorem map_mulVec_real_convex_eq_interior {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    ((stdGaussianPi ι).map (fun z ↦ L *ᵥ z)).real K =
      ((stdGaussianPi ι).map (fun z ↦ L *ᵥ z)).real (interior K) := by
  rw [map_mulVec_eq_map_affine_zero L]
  exact map_affine_real_convex_eq_interior L hL 0 hK

/-- `map_affine_real_convex_eq_closure` with `c = 0` (infrastructure). -/
theorem map_mulVec_real_convex_eq_closure {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    ((stdGaussianPi ι).map (fun z ↦ L *ᵥ z)).real K =
      ((stdGaussianPi ι).map (fun z ↦ L *ᵥ z)).real (closure K) := by
  rw [map_mulVec_eq_map_affine_zero L]
  exact map_affine_real_convex_eq_closure L hL 0 hK

end Linear

/-! ## Non-vacuity -/

/-- Non-vacuity: the shell bound applies to the half-plane `{x | x 0 ≤ 0}` in `ℝ²`. -/
example : (stdGaussianPi (Fin 2)).real
    (cthickening 1 {x : Fin 2 → ℝ | x 0 ≤ 0} ∩
      cthickening 1 (interior {x : Fin 2 → ℝ | x 0 ≤ 0})ᶜ) ≤
    4 * (Fintype.card (Fin 2) : ℝ) ^ 2 * 1 / √(2 * π) :=
  stdGaussianPi_convexShell_le (convex_halfSpace_le (f := fun x : Fin 2 → ℝ ↦ x 0)
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 0) zero_le_one

/-- Non-vacuity: the affine bound applies with `L = 1` (so `IsUnit L.det` holds). -/
example : ((stdGaussianPi (Fin 2)).map (fun z ↦ 0 + (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ z)).real
    (cthickening 1 {x : Fin 2 → ℝ | x 0 ≤ 0} ∩
      cthickening 1 (interior {x : Fin 2 → ℝ | x 0 ≤ 0})ᶜ) ≤
    4 * (Fintype.card (Fin 2) : ℝ) ^ 2 *
      matrixMaxRowAbsSum (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 / √(2 * π) :=
  map_affine_convexShell_le 1 (by simp) 0 (convex_halfSpace_le (f := fun x : Fin 2 → ℝ ↦ x 0)
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 0) zero_le_one

end StatisticalRL.Probability
