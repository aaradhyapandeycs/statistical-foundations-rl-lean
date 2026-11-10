import Formalization.Probability.SteinRandomConcentration

/-!
# Randomized concentration for polyhedral functions of bounded vector sums

Infrastructure. Setting of `BerryEsseenStein`: a finite product of finite laws `p i` on
coordinates `ω i ∈ X i`, with expectation `pexp p`. The summands are vectors
`ξ i (ω i) : κ → ℝ` (finite coordinate type `κ`, sup norm), independent, mean zero and bounded
by `δ` in the sup norm. `W = vsum ξ = ∑ᵢ ξᵢ(ωᵢ)`.

The test function is a polyhedral convex function `φ = polyPhi 𝓕 h𝓕`, the maximum of finitely
many affine forms `x ↦ ⟨v, x⟩ - c` with `∑ⱼ |vⱼ| = 1`; `vsel` picks a maximizing direction, which
is a unit-ℓ¹ subgradient.

Main results:
* `fr_mul_sub_fr_mul_nonneg`, `three_quarters_sq_le_fr_mul_sub_fr_mul` — a scalar second-order
  lower bound for the ramp `fr a b δ` (the core inequality of the argument);
* `pexp_dotProduct_eq_zero_of_update` — vector Stein identity with a random factor not
  depending on `ω i`;
* `sub_devSum_le_sum_sq_dotProduct` — pathwise uniform-in-direction lower bound
  `∑ᵢ ⟨v, ξᵢ⟩² ≥ λ - ∑ⱼₖ |Sⱼₖ - Σⱼₖ|`;
* `pexp_intervalInd_polyhedral_le` — randomized shell bound
  `λ P(a ≤ φ(W) ≤ b) ≤ (4/3)(E‖W‖(b - a) + 2δ E‖W‖ + ∑ᵢ E‖ξᵢ‖(|a - aᵢ| + |b - bᵢ|)) + E m`
  for random endpoints `a ≤ b` and leave-one-out endpoints `aᵢ, bᵢ` not depending on `ω i`;
* `pexp_devSum_le`, `pexp_norm_vsum_le` — `E m ≤ δ |κ| ∑ⱼ σⱼ` and `E‖W‖ ≤ ∑ⱼ σⱼ`.

The argument is self-contained and uses that the summands are bounded by the smoothing width
`δ`, so no truncation is needed.
-/

open MeasureTheory ProbabilityTheory Real Set Finset Matrix

namespace StatisticalRL.Probability.Stein

namespace Polyhedral

/-! ## The ramp `fr` -/

/-- The ramp `fr a b δ r = min (max (r - a + δ) 0) (b - a + 2δ)`. -/
noncomputable def fr (a b δ r : ℝ) : ℝ := min (max (r - a + δ) 0) (b - a + 2 * δ)

theorem fr_nonneg {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) (r : ℝ) : 0 ≤ fr a b δ r :=
  le_min (le_max_right _ _) (by linarith)

theorem fr_le (a b δ r : ℝ) : fr a b δ r ≤ b - a + 2 * δ := min_le_right _ _

theorem fr_mono (a b δ : ℝ) : Monotone (fr a b δ) := fun r r' h ↦
  min_le_min_right _ (max_le_max_right _ (by linarith))

theorem fr_eq_of_mem {a b δ r : ℝ} (h1 : a - δ ≤ r) (h2 : r ≤ b + δ) :
    fr a b δ r = r - a + δ := by
  unfold fr
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

/-- The ramp is Lipschitz in its endpoints: `|fr a b δ r - fr a' b' δ r| ≤ |a - a'| + |b - b'|`. -/
theorem abs_fr_sub_fr_le (a b a' b' δ r : ℝ) :
    |fr a b δ r - fr a' b' δ r| ≤ |a - a'| + |b - b'| := by
  unfold fr
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · rw [show r - a + δ - (r - a' + δ) = -(a - a') by ring, abs_neg]
      linarith [abs_nonneg (b - b')]
    · simp only [sub_self, abs_zero]; positivity
  · rw [show b - a + 2 * δ - (b' - a' + 2 * δ) = (b - b') + -(a - a') by ring]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_neg, add_comm]

/-! ## The scalar second-order lower bound -/

/-- Off the shell: if `s' ≤ t ≤ s`, then `fr r · s - fr (r - t) · s' ≥ 0`. -/
theorem fr_mul_sub_fr_mul_nonneg {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) {r s s' t : ℝ}
    (hts : t ≤ s) (hst : s' ≤ t) : 0 ≤ fr a b δ r * s - fr a b δ (r - t) * s' := by
  have h0 := fr_nonneg hab hδ r
  have h1 := fr_nonneg hab hδ (r - t)
  have hA : fr a b δ (r - t) * s' ≤ fr a b δ (r - t) * t := mul_le_mul_of_nonneg_left hst h1
  have hB : fr a b δ r * t ≤ fr a b δ r * s := mul_le_mul_of_nonneg_left hts h0
  have hC : 0 ≤ t * (fr a b δ r - fr a b δ (r - t)) := by
    rcases le_or_gt 0 t with ht | ht
    · exact mul_nonneg ht (sub_nonneg.2 (fr_mono a b δ (by linarith)))
    · exact mul_nonneg_of_nonpos_of_nonpos ht.le
        (sub_nonpos.2 (fr_mono a b δ (by linarith)))
  nlinarith

/-- On the shell: if `a ≤ r ≤ b`, `s' ≤ t ≤ s`, `|s| ≤ δ` and `|t| ≤ δ`, then
`fr r · s - fr (r - t) · s' ≥ (3/4) s²`. -/
theorem three_quarters_sq_le_fr_mul_sub_fr_mul {a b δ r s s' t : ℝ} (hr1 : a ≤ r) (hr2 : r ≤ b)
    (hts : t ≤ s) (hst : s' ≤ t) (hs : |s| ≤ δ) (ht : |t| ≤ δ) :
    (3 / 4) * s ^ 2 ≤ fr a b δ r * s - fr a b δ (r - t) * s' := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hs
  obtain ⟨ht1, ht2⟩ := abs_le.1 ht
  have hab : a ≤ b := hr1.trans hr2
  have hf1 : fr a b δ r = r - a + δ := fr_eq_of_mem (by linarith) (by linarith)
  have hf2 : fr a b δ (r - t) = r - t - a + δ := fr_eq_of_mem (by linarith) (by linarith)
  have h1 := fr_nonneg hab hδ (r - t)
  have hA : fr a b δ (r - t) * s' ≤ fr a b δ (r - t) * t := mul_le_mul_of_nonneg_left hst h1
  rw [hf2] at hA
  rw [hf1, hf2]
  -- `Q ≥ (r - a + δ)(s - t) + t² ≥ |s|(s - t) + t²`
  have hc : |s| * (s - t) ≤ (r - a + δ) * (s - t) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  rcases le_or_gt 0 s with hs0 | hs0
  · rw [abs_of_nonneg hs0] at hc
    nlinarith [sq_nonneg (t - s / 2)]
  · rw [abs_of_neg hs0] at hc
    nlinarith [mul_le_mul_of_nonpos_left hts hs0.le]

/-! ## Polyhedral functions -/

section Poly

variable {κ : Type*} [Fintype κ]

/-- `|⟨v, z⟩| ≤ (∑ⱼ |vⱼ|) ‖z‖` (sup norm). -/
theorem abs_dotProduct_le (v z : κ → ℝ) : |v ⬝ᵥ z| ≤ (∑ j, |v j|) * ‖z‖ := by
  calc |v ⬝ᵥ z| ≤ ∑ j, |v j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |v j| * ‖z‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm z j) (abs_nonneg _)
    _ = (∑ j, |v j|) * ‖z‖ := by rw [Finset.sum_mul]

/-- The sup norm is at most the ℓ¹ norm. -/
theorem norm_le_sum_abs (x : κ → ℝ) : ‖x‖ ≤ ∑ j, |x j| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)).2 fun j ↦ by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j ↦ |x j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)

/-- The polyhedral function `φ x = max_{q ∈ 𝓕} (⟨q.1, x⟩ - q.2)`. -/
noncomputable def polyPhi (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x : κ → ℝ) : ℝ :=
  𝓕.sup' h𝓕 fun q ↦ q.1 ⬝ᵥ x - q.2

/-- A maximizing affine form of `polyPhi` at `x`. -/
noncomputable def qsel (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x : κ → ℝ) :
    (κ → ℝ) × ℝ :=
  Classical.choose (Finset.exists_mem_eq_sup' h𝓕 fun q ↦ q.1 ⬝ᵥ x - q.2)

/-- The direction of a maximizing affine form: a subgradient of `polyPhi` at `x`. -/
noncomputable def vsel (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x : κ → ℝ) : κ → ℝ :=
  (qsel 𝓕 h𝓕 x).1

theorem qsel_mem (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x : κ → ℝ) :
    qsel 𝓕 h𝓕 x ∈ 𝓕 :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' h𝓕 fun q ↦ q.1 ⬝ᵥ x - q.2)).1

theorem polyPhi_eq_qsel (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x : κ → ℝ) :
    polyPhi 𝓕 h𝓕 x = vsel 𝓕 h𝓕 x ⬝ᵥ x - (qsel 𝓕 h𝓕 x).2 :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' h𝓕 fun q ↦ q.1 ⬝ᵥ x - q.2)).2

theorem sum_abs_vsel {𝓕 : Finset ((κ → ℝ) × ℝ)} (h𝓕 : 𝓕.Nonempty)
    (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) (x : κ → ℝ) : ∑ j, |vsel 𝓕 h𝓕 x j| = 1 :=
  h𝓕1 _ (qsel_mem 𝓕 h𝓕 x)

theorem abs_vsel_dotProduct_le {𝓕 : Finset ((κ → ℝ) × ℝ)} (h𝓕 : 𝓕.Nonempty)
    (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) (x z : κ → ℝ) : |vsel 𝓕 h𝓕 x ⬝ᵥ z| ≤ ‖z‖ := by
  simpa [sum_abs_vsel h𝓕 h𝓕1 x] using abs_dotProduct_le (vsel 𝓕 h𝓕 x) z

/-- **Subgradient inequality**: `φ y ≥ φ x + ⟨vsel x, y - x⟩`. -/
theorem polyPhi_add_vsel_le (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x y : κ → ℝ) :
    polyPhi 𝓕 h𝓕 x + vsel 𝓕 h𝓕 x ⬝ᵥ (y - x) ≤ polyPhi 𝓕 h𝓕 y := by
  have h := Finset.le_sup' (fun q : (κ → ℝ) × ℝ ↦ q.1 ⬝ᵥ y - q.2) (qsel_mem 𝓕 h𝓕 x)
  rw [polyPhi_eq_qsel, dotProduct_sub]
  unfold polyPhi
  unfold vsel at *
  linarith

/-- `polyPhi` is `1`-Lipschitz for the sup norm. -/
theorem abs_polyPhi_sub_le {𝓕 : Finset ((κ → ℝ) × ℝ)} (h𝓕 : 𝓕.Nonempty)
    (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) (x y : κ → ℝ) :
    |polyPhi 𝓕 h𝓕 x - polyPhi 𝓕 h𝓕 y| ≤ ‖x - y‖ := by
  have h1 := polyPhi_add_vsel_le 𝓕 h𝓕 x y
  have h2 := polyPhi_add_vsel_le 𝓕 h𝓕 y x
  have h3 := abs_vsel_dotProduct_le h𝓕 h𝓕1 x (y - x)
  have h4 := abs_vsel_dotProduct_le h𝓕 h𝓕1 y (x - y)
  rw [norm_sub_rev] at h3
  rw [abs_le]
  constructor <;> linarith [abs_le.1 h3, abs_le.1 h4]

/-- Deterministic core of the shell bound. For vectors `y i` with `‖y i‖ ≤ δ`, `w = ∑ᵢ y i`,
endpoints `a ≤ b` and arbitrary `aᵢ, bᵢ`, and `λ - m ≤ ∑ᵢ ⟨v, y i⟩²` for every unit-ℓ¹ `v`
(with `m ≥ 0`), the Stein increments satisfy
`(3/4)(λ 1{a ≤ φ w ≤ b} - m) - ∑ᵢ ‖y i‖(|a - aᵢ| + |b - bᵢ|) ≤
  ∑ᵢ (fr a b δ (φ w) ⟨vsel w, y i⟩ - fr aᵢ bᵢ δ (φ (w - y i)) ⟨vsel (w - y i), y i⟩)`. -/
theorem polyhedral_increment_sum_ge {ι : Type*} [Fintype ι] {𝓕 : Finset ((κ → ℝ) × ℝ)}
    (h𝓕 : 𝓕.Nonempty) (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (y : ι → κ → ℝ) (hy : ∀ i, ‖y i‖ ≤ δ) {a b : ℝ} (hab : a ≤ b) (ai bi : ι → ℝ)
    {lam m : ℝ} (hm : 0 ≤ m)
    (hq : ∀ v : κ → ℝ, ∑ j, |v j| = 1 → lam - m ≤ ∑ i, (v ⬝ᵥ y i) ^ 2) :
    (3 / 4) * (lam * intervalInd a b (polyPhi 𝓕 h𝓕 (∑ i, y i)) - m) -
        ∑ i, ‖y i‖ * (|a - ai i| + |b - bi i|) ≤
      ∑ i, (fr a b δ (polyPhi 𝓕 h𝓕 (∑ i, y i)) * (vsel 𝓕 h𝓕 (∑ i, y i) ⬝ᵥ y i) -
        fr (ai i) (bi i) δ (polyPhi 𝓕 h𝓕 ((∑ i, y i) - y i)) *
          (vsel 𝓕 h𝓕 ((∑ i, y i) - y i) ⬝ᵥ y i)) := by
  set w := ∑ i, y i with hw
  set φ := polyPhi 𝓕 h𝓕 with hφ
  set vs := vsel 𝓕 h𝓕 with hvs
  -- split each increment into the main part and the endpoint error
  have hsplit : ∀ i, fr a b δ (φ w) * (vs w ⬝ᵥ y i) -
      fr (ai i) (bi i) δ (φ (w - y i)) * (vs (w - y i) ⬝ᵥ y i) =
      (fr a b δ (φ w) * (vs w ⬝ᵥ y i) - fr a b δ (φ w - (φ w - φ (w - y i))) *
        (vs (w - y i) ⬝ᵥ y i)) +
      (fr a b δ (φ (w - y i)) - fr (ai i) (bi i) δ (φ (w - y i))) *
        (vs (w - y i) ⬝ᵥ y i) := by
    intro i
    rw [sub_sub_cancel]
    ring
  have herr : ∀ i, -(‖y i‖ * (|a - ai i| + |b - bi i|)) ≤
      (fr a b δ (φ (w - y i)) - fr (ai i) (bi i) δ (φ (w - y i))) *
        (vs (w - y i) ⬝ᵥ y i) := by
    intro i
    refine neg_le_of_abs_le ?_
    rw [abs_mul, mul_comm]
    exact mul_le_mul (abs_vsel_dotProduct_le h𝓕 h𝓕1 _ _)
      (abs_fr_sub_fr_le _ _ _ _ _ _) (abs_nonneg _) (norm_nonneg _)
  -- the facts `s' ≤ t ≤ s`, `|s| ≤ δ`, `|t| ≤ δ`
  have hts : ∀ i, φ w - φ (w - y i) ≤ vs w ⬝ᵥ y i := by
    intro i
    have h := polyPhi_add_vsel_le 𝓕 h𝓕 w (w - y i)
    rw [sub_sub_cancel_left, dotProduct_neg] at h
    linarith
  have hst : ∀ i, vs (w - y i) ⬝ᵥ y i ≤ φ w - φ (w - y i) := by
    intro i
    have h := polyPhi_add_vsel_le 𝓕 h𝓕 (w - y i) w
    rw [sub_sub_cancel] at h
    linarith
  have hsδ : ∀ i, |vs w ⬝ᵥ y i| ≤ δ := fun i ↦
    (abs_vsel_dotProduct_le h𝓕 h𝓕1 _ _).trans (hy i)
  have htδ : ∀ i, |φ w - φ (w - y i)| ≤ δ := fun i ↦ by
    have h := abs_polyPhi_sub_le h𝓕 h𝓕1 w (w - y i)
    rw [sub_sub_cancel] at h
    exact h.trans (hy i)
  have hmain : (3 / 4) * (lam * intervalInd a b (φ w) - m) ≤
      ∑ i, (fr a b δ (φ w) * (vs w ⬝ᵥ y i) - fr a b δ (φ w - (φ w - φ (w - y i))) *
        (vs (w - y i) ⬝ᵥ y i)) := by
    unfold intervalInd
    split_ifs with hA
    · calc (3 / 4) * (lam * 1 - m) ≤ (3 / 4) * ∑ i, (vs w ⬝ᵥ y i) ^ 2 := by
            have := hq (vs w) (sum_abs_vsel h𝓕 h𝓕1 w)
            linarith
        _ = ∑ i, (3 / 4) * (vs w ⬝ᵥ y i) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦
            three_quarters_sq_le_fr_mul_sub_fr_mul hA.1 hA.2 (hts i) (hst i) (hsδ i) (htδ i)
    · have h0 : 0 ≤ ∑ i, (fr a b δ (φ w) * (vs w ⬝ᵥ y i) -
          fr a b δ (φ w - (φ w - φ (w - y i))) * (vs (w - y i) ⬝ᵥ y i)) :=
        Finset.sum_nonneg fun i _ ↦ fr_mul_sub_fr_mul_nonneg hab hδ (hts i) (hst i)
      linarith
  simp only [hsplit, Finset.sum_add_distrib]
  have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ herr i
  simp only [Finset.sum_neg_distrib] at h2
  linarith

theorem sq_dotProduct_eq (v y : κ → ℝ) :
    (v ⬝ᵥ y) ^ 2 = ∑ j, ∑ k, v j * v k * (y j * y k) := by
  rw [sq, dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

theorem sum_sum_mul_sum_comm {α : Type*} (v : κ → ℝ) (t : Finset α) (f : α → κ → κ → ℝ) :
    ∑ j, ∑ k, v j * v k * ∑ i ∈ t, f i j k = ∑ i ∈ t, ∑ j, ∑ k, v j * v k * f i j k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm]
  exact Finset.sum_comm

end Poly

/-! ## Vector sums of independent summands -/

section Vector

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  {κ : Type*} [Fintype κ]

/-- The vector sum `W = ∑ᵢ ξᵢ(ωᵢ)`. -/
def vsum (ξ : ∀ i, X i → κ → ℝ) (ω : ∀ i, X i) : κ → ℝ := ∑ i, ξ i (ω i)

omit [∀ i, Fintype (X i)] [Fintype κ] in
/-- The leave-one-out sum `W - ξᵢ(ωᵢ)` does not depend on `ω i`. -/
theorem vsum_update_sub (ξ : ∀ i, X i → κ → ℝ) (i : ι) (ω : ∀ i, X i) (c : X i) :
    vsum ξ (Function.update ω i c) - ξ i (Function.update ω i c i) = vsum ξ ω - ξ i (ω i) := by
  funext j
  have h := looStat_update (fun i x ↦ ξ i x j) i ω c
  simpa [looStat, sumStat, vsum, Finset.sum_apply] using h

/-- Entry `(j, k)` of the empirical-minus-population covariance:
`∑ᵢ (ξᵢⱼ(ωᵢ) ξᵢₖ(ωᵢ) - E ξᵢⱼ ξᵢₖ)`. -/
def covDev (p : ∀ i, X i → ℝ) (ξ : ∀ i, X i → κ → ℝ) (ω : ∀ i, X i) (j k : κ) : ℝ :=
  ∑ i, (ξ i (ω i) j * ξ i (ω i) k - ∑ x, p i x * (ξ i x j * ξ i x k))

/-- The deviation size `m = ∑ⱼₖ |Sⱼₖ - Σⱼₖ|`. -/
def devSum (p : ∀ i, X i → ℝ) (ξ : ∀ i, X i → κ → ℝ) (ω : ∀ i, X i) : ℝ :=
  ∑ j, ∑ k, |covDev p ξ ω j k|

omit [DecidableEq ι] in
theorem devSum_nonneg (p : ∀ i, X i → ℝ) (ξ : ∀ i, X i → κ → ℝ) (ω : ∀ i, X i) :
    0 ≤ devSum p ξ ω :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

omit [DecidableEq ι] in
/-- `∑ᵢ ⟨v, ξᵢ(ωᵢ)⟩² = ∑ᵢ E⟨v, ξᵢ⟩² + ∑ⱼₖ vⱼ vₖ (Sⱼₖ - Σⱼₖ)`. -/
theorem sum_sq_dotProduct_eq (p : ∀ i, X i → ℝ) (ξ : ∀ i, X i → κ → ℝ) (ω : ∀ i, X i)
    (v : κ → ℝ) :
    ∑ i, (v ⬝ᵥ ξ i (ω i)) ^ 2 = ∑ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2 +
      ∑ j, ∑ k, v j * v k * covDev p ξ ω j k := by
  have hx : ∀ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2 =
      ∑ j, ∑ k, v j * v k * ∑ x, p i x * (ξ i x j * ξ i x k) := by
    intro i
    rw [sum_sum_mul_sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [sq_dotProduct_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  unfold covDev
  rw [sum_sum_mul_sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hx, sq_dotProduct_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

omit [DecidableEq ι] in
/-- **Uniform quadratic-form lower bound** (pathwise): if `λ ≤ ∑ᵢ E⟨v, ξᵢ⟩²` for every `v` with
`∑ⱼ |vⱼ| = 1`, then `∑ᵢ ⟨v, ξᵢ(ωᵢ)⟩² ≥ λ - ∑ⱼₖ |Sⱼₖ - Σⱼₖ|` for every such `v` and every `ω`. -/
theorem sub_devSum_le_sum_sq_dotProduct (p : ∀ i, X i → ℝ) (ξ : ∀ i, X i → κ → ℝ) {lam : ℝ}
    (hlam : ∀ v : κ → ℝ, ∑ j, |v j| = 1 → lam ≤ ∑ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2)
    (ω : ∀ i, X i) (v : κ → ℝ) (hv : ∑ j, |v j| = 1) :
    lam - devSum p ξ ω ≤ ∑ i, (v ⬝ᵥ ξ i (ω i)) ^ 2 := by
  rw [sum_sq_dotProduct_eq p ξ ω v]
  have hvj : ∀ j, |v j| ≤ 1 := fun j ↦ hv ▸
    Finset.single_le_sum (f := fun j ↦ |v j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)
  have hbd : |∑ j, ∑ k, v j * v k * covDev p ξ ω j k| ≤ devSum p ξ ω := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [abs_mul, abs_mul]
    have h1 : |v j| * |v k| ≤ 1 := by
      nlinarith [abs_nonneg (v j), abs_nonneg (v k), hvj j, hvj k]
    nlinarith [abs_nonneg (covDev p ξ ω j k)]
  linarith [hlam v hv, (abs_le.1 hbd).1]

omit [DecidableEq ι] in
/-- **Vector Stein identity with a random factor.** If `G` does not depend on the coordinate
`ω i` and `ξᵢ` has mean zero, then `E⟨G, ξᵢ(ωᵢ)⟩ = 0`. -/
theorem pexp_dotProduct_eq_zero_of_update [DecidableEq ι] {p : ∀ i, X i → ℝ}
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → κ → ℝ}
    (hmean : ∀ i j, ∑ x, p i x * ξ i x j = 0) (i : ι) (G : (∀ j, X j) → κ → ℝ)
    (hG : ∀ ω c, G (Function.update ω i c) = G ω) :
    pexp p (fun ω ↦ G ω ⬝ᵥ ξ i (ω i)) = 0 := by
  unfold dotProduct
  rw [pexp_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have h := pexp_mul_eq_zero_of_update hp1 (ξ := fun i x ↦ ξ i x j) (fun i ↦ hmean i j) i
    (fun ω ↦ G ω j) (fun ω c ↦ by simp only [hG])
  simpa only [mul_comm] using h

/-- **Randomized shell bound for a polyhedral function.** Let the summands be mean zero,
bounded by `δ` in the sup norm, and satisfy `λ ≤ ∑ᵢ E⟨v, ξᵢ⟩²` for every `v` with
`∑ⱼ |vⱼ| = 1`. Let `φ = polyPhi 𝓕 h𝓕` with unit-ℓ¹ directions, `a ≤ b` random endpoints, and
`aᵢ, bᵢ` random variables not depending on the coordinate `ω i`. Then

`λ P(a ≤ φ(W) ≤ b) ≤ (4/3)(E[‖W‖(b - a)] + 2δ E‖W‖ + ∑ᵢ E[‖ξᵢ‖(|a - aᵢ| + |b - bᵢ|)]) + E m`,

with `m = devSum p ξ`. -/
theorem pexp_intervalInd_polyhedral_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → κ → ℝ}
    (hmean : ∀ i j, ∑ x, p i x * ξ i x j = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbd : ∀ i x, ‖ξ i x‖ ≤ δ) {lam : ℝ}
    (hlam : ∀ v : κ → ℝ, ∑ j, |v j| = 1 → lam ≤ ∑ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2)
    (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1)
    (a b : (∀ i, X i) → ℝ) (hab : ∀ ω, a ω ≤ b ω) (ai bi : ι → (∀ i, X i) → ℝ)
    (hai : ∀ i ω c, ai i (Function.update ω i c) = ai i ω)
    (hbi : ∀ i ω c, bi i (Function.update ω i c) = bi i ω) :
    lam * pexp p (fun ω ↦ intervalInd (a ω) (b ω) (polyPhi 𝓕 h𝓕 (vsum ξ ω))) ≤
      (4 / 3) * (pexp p (fun ω ↦ ‖vsum ξ ω‖ * (b ω - a ω)) +
          2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) +
          ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * (|a ω - ai i ω| + |b ω - bi i ω|))) +
        pexp p (devSum p ξ) := by
  set W := vsum ξ with hW
  set φ := polyPhi 𝓕 h𝓕 with hφ
  set vs := vsel 𝓕 h𝓕 with hvs
  set P := pexp p (fun ω ↦ intervalInd (a ω) (b ω) (φ (W ω))) with hP
  set R := ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * (|a ω - ai i ω| + |b ω - bi i ω|)) with hR
  set Z := pexp p (fun ω ↦ fr (a ω) (b ω) δ (φ (W ω)) * (vs (W ω) ⬝ᵥ W ω)) with hZ
  -- upper bound
  have hup : Z ≤ pexp p (fun ω ↦ ‖W ω‖ * (b ω - a ω)) + 2 * δ * pexp p (fun ω ↦ ‖W ω‖) := by
    rw [← pexp_const_mul, ← pexp_add]
    refine pexp_mono hp0 fun ω ↦ ?_
    have h1 := fr_nonneg (hab ω) hδ (φ (W ω))
    have h2 := fr_le (a ω) (b ω) δ (φ (W ω))
    have h3 := (abs_le.1 (abs_vsel_dotProduct_le h𝓕 h𝓕1 (W ω) (W ω))).2
    have h4 := norm_nonneg (W ω)
    calc fr (a ω) (b ω) δ (φ (W ω)) * (vs (W ω) ⬝ᵥ W ω)
        ≤ fr (a ω) (b ω) δ (φ (W ω)) * ‖W ω‖ := mul_le_mul_of_nonneg_left h3 h1
      _ ≤ (b ω - a ω + 2 * δ) * ‖W ω‖ := mul_le_mul_of_nonneg_right h2 h4
      _ = _ := by ring
  -- Stein decomposition
  have hzero : ∀ i, pexp p (fun ω ↦ (fr (ai i ω) (bi i ω) δ (φ (W ω - ξ i (ω i))) •
      vs (W ω - ξ i (ω i))) ⬝ᵥ ξ i (ω i)) = 0 := fun i ↦
    pexp_dotProduct_eq_zero_of_update hp1 hmean i _ fun ω c ↦ by
      simp only [hW, hai, hbi, vsum_update_sub]
  have hdecomp : Z = pexp p (fun ω ↦ ∑ i, (fr (a ω) (b ω) δ (φ (W ω)) * (vs (W ω) ⬝ᵥ ξ i (ω i)) -
      fr (ai i ω) (bi i ω) δ (φ (W ω - ξ i (ω i))) * (vs (W ω - ξ i (ω i)) ⬝ᵥ ξ i (ω i)))) := by
    rw [pexp_sum]
    have h1 : Z = ∑ i, pexp p (fun ω ↦ fr (a ω) (b ω) δ (φ (W ω)) * (vs (W ω) ⬝ᵥ ξ i (ω i))) := by
      rw [hZ, ← pexp_sum]
      congr 1
      funext ω
      rw [← Finset.mul_sum, ← dotProduct_sum]
      rfl
    rw [h1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pexp_sub]
    have h2 := hzero i
    simp only [smul_dotProduct, smul_eq_mul] at h2
    rw [h2, sub_zero]
  -- pathwise lower bound
  have hlow : (3 / 4) * (lam * P - pexp p (devSum p ξ)) - R ≤ Z := by
    rw [hdecomp, hR, hP, ← pexp_const_mul, ← pexp_sub, ← pexp_const_mul, ← pexp_sum,
      ← pexp_sub]
    refine pexp_mono hp0 fun ω ↦ ?_
    exact polyhedral_increment_sum_ge h𝓕 h𝓕1 hδ (fun i ↦ ξ i (ω i)) (fun i ↦ hbd i (ω i))
      (hab ω) (fun i ↦ ai i ω) (fun i ↦ bi i ω) (devSum_nonneg p ξ ω)
      (fun v hv ↦ sub_devSum_le_sum_sq_dotProduct p ξ hlam ω v hv)
  linarith

/-- **Deviation bound.** For summands bounded by `δ` in the sup norm (no mean-zero hypothesis: the centring is done inside the proof; `σⱼ` is the uncentred root second moment),
`E m ≤ δ |κ| ∑ⱼ σⱼ` with `σⱼ = √(∑ᵢ E ξᵢⱼ²)` and `m = devSum p ξ`. -/
theorem pexp_devSum_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → κ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hbd : ∀ i x, ‖ξ i x‖ ≤ δ) :
    pexp p (devSum p ξ) ≤
      δ * Fintype.card κ * ∑ j, √(∑ i, ∑ x, p i x * ξ i x j ^ 2) := by
  have hentry : ∀ j k, pexp p (fun ω ↦ |covDev p ξ ω j k|) ≤
      δ * √(∑ i, ∑ x, p i x * ξ i x j ^ 2) := by
    intro j k
    set f : ∀ i, X i → ℝ := fun i x ↦ ξ i x j * ξ i x k with hf
    set u : ∀ i, X i → ℝ := fun i x ↦ f i x - ∑ y, p i y * f i y with hu
    have hcov : ∀ ω, covDev p ξ ω j k = sumStat u ω := fun ω ↦ rfl
    have humean : ∀ i, ∑ x, p i x * u i x = 0 := by
      intro i
      simp only [hu, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, sub_self]
    have hsq : pexp p (fun ω ↦ covDev p ξ ω j k ^ 2) ≤
        δ ^ 2 * ∑ i, ∑ x, p i x * ξ i x j ^ 2 := by
      simp only [hcov]
      rw [pexp_sumStat_sq hp1 humean, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hv := sum_mul_sub_mean_sq (hp1 i) (f i)
      calc ∑ x, p i x * u i x ^ 2 ≤ ∑ x, p i x * f i x ^ 2 := by
            simp only [hu]
            rw [hv]
            nlinarith [sq_nonneg (∑ x, p i x * f i x)]
        _ ≤ ∑ x, p i x * (δ ^ 2 * ξ i x j ^ 2) := Finset.sum_le_sum fun x _ ↦ by
            refine mul_le_mul_of_nonneg_left ?_ (hp0 i x)
            have hk : |ξ i x k| ≤ δ := by
              have := norm_le_pi_norm (ξ i x) k
              rw [Real.norm_eq_abs] at this
              exact this.trans (hbd i x)
            have hk2 : ξ i x k ^ 2 ≤ δ ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk 2
            simp only [hf, mul_pow]
            nlinarith [sq_nonneg (ξ i x j)]
        _ = δ ^ 2 * ∑ x, p i x * ξ i x j ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ ↦ by ring
    have h1 := (sq_pexp_abs_le hp0 hp1 fun ω ↦ covDev p ξ ω j k).trans hsq
    have h0 : 0 ≤ pexp p (fun ω ↦ |covDev p ξ ω j k|) := pexp_nonneg hp0 fun ω ↦ abs_nonneg _
    have hS : 0 ≤ ∑ i, ∑ x, p i x * ξ i x j ^ 2 := Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp0 i x) (sq_nonneg _)
    calc pexp p (fun ω ↦ |covDev p ξ ω j k|) ≤ √(δ ^ 2 * ∑ i, ∑ x, p i x * ξ i x j ^ 2) :=
          Real.le_sqrt_of_sq_le h1
      _ = δ * √(∑ i, ∑ x, p i x * ξ i x j ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]
  calc pexp p (devSum p ξ) = ∑ j, ∑ k, pexp p (fun ω ↦ |covDev p ξ ω j k|) := by
        unfold devSum
        rw [pexp_sum]
        exact Finset.sum_congr rfl fun j _ ↦ pexp_sum _ _ _
    _ ≤ ∑ j, ∑ _k : κ, δ * √(∑ i, ∑ x, p i x * ξ i x j ^ 2) :=
        Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦ hentry j k
    _ = δ * Fintype.card κ * ∑ j, √(∑ i, ∑ x, p i x * ξ i x j ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **First moment of the sup norm.** For mean-zero summands, `E‖W‖ ≤ ∑ⱼ σⱼ` with
`σⱼ = √(∑ᵢ E ξᵢⱼ²)`. -/
theorem pexp_norm_vsum_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → κ → ℝ}
    (hmean : ∀ i j, ∑ x, p i x * ξ i x j = 0) :
    pexp p (fun ω ↦ ‖vsum ξ ω‖) ≤ ∑ j, √(∑ i, ∑ x, p i x * ξ i x j ^ 2) := by
  have hcoord : ∀ j, pexp p (fun ω ↦ |vsum ξ ω j|) ≤ √(∑ i, ∑ x, p i x * ξ i x j ^ 2) := by
    intro j
    have hW : ∀ ω, vsum ξ ω j = sumStat (fun i x ↦ ξ i x j) ω := fun ω ↦ by
      simp [vsum, sumStat, Finset.sum_apply]
    have h2 : pexp p (fun ω ↦ vsum ξ ω j ^ 2) = ∑ i, ∑ x, p i x * ξ i x j ^ 2 := by
      simp only [hW]
      exact pexp_sumStat_sq hp1 (fun i ↦ hmean i j)
    exact Real.le_sqrt_of_sq_le ((sq_pexp_abs_le hp0 hp1 _).trans h2.le)
  calc pexp p (fun ω ↦ ‖vsum ξ ω‖) ≤ pexp p (fun ω ↦ ∑ j, |vsum ξ ω j|) :=
        pexp_mono hp0 fun ω ↦ norm_le_sum_abs _
    _ = ∑ j, pexp p (fun ω ↦ |vsum ξ ω j|) := pexp_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hcoord j

end Vector

end Polyhedral

end StatisticalRL.Probability.Stein
