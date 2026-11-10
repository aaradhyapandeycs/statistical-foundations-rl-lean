import Formalization.Probability.SteinPolyhedralConcentration
import Formalization.Analysis.PolyhedralSeparation

/-!
# Nonlinear transfer over convex sets for bounded vector sums

Infrastructure (not a source result). Setting of `SteinPolyhedralConcentration`: a finite product
of finite laws `p i` with expectation `pexp p`, independent mean-zero vector summands
`ξ i (ω i) : κ → ℝ` bounded by `δ` in the sup norm, and `W = vsum ξ = ∑ᵢ ξᵢ(ωᵢ)`. Let
`D : Ω → κ → ℝ` be an arbitrary perturbation and `Dᵢ` leave-one-out versions of it that do not
depend on the coordinate `ω i` (for instance `Dᵢ ω = D (update ω i (xs i))`).

If `λ > 0` and `λ ≤ ∑ᵢ E⟨v, ξᵢ⟩²` for every `v` with `∑ⱼ |vⱼ| = 1`, then for every convex
`C ⊆ κ → ℝ` (no closedness or measurability is needed: the sample space is finite)

`|P(W + D ∈ C) - P(W ∈ C)| ≤ λ⁻¹ ((4/3)(E‖W‖‖D‖ + 2δ E‖W‖ + ∑ᵢ E‖ξᵢ‖ |‖D‖ - ‖Dᵢ‖|) + E m)`,

with `m = devSum p ξ = ∑ⱼₖ |Sⱼₖ - Σⱼₖ|`.

Proof: the finitely many points `W ω` and `W ω + D ω` are classified exactly by a polyhedral
function `φ` with unit-ℓ¹ forms (`exists_polyhedral_repr` of `PolyhedralSeparation`), which is
`1`-Lipschitz for the sup norm. Pathwise,
`1_C(W + D) ≤ 1_C(W) + 1{0 ≤ φ(W) ≤ ‖D‖}` and `1_C(W) ≤ 1_C(W + D) + 1{-‖D‖ ≤ φ(W) ≤ 0}`,
and both shell probabilities are bounded by the randomized shell bound
`pexp_intervalInd_polyhedral_le`. The argument is a self-contained variant for bounded summands
and fixed dimension; its constants are not those of any published theorem.

Main results:
* `indicator_add_le_indicator_add_intervalInd`, `indicator_le_indicator_add_add_intervalInd` —
  the pathwise sandwich;
* `abs_pexp_convex_add_sub_le` — the transfer bound with abstract leave-one-out perturbations;
* `abs_pexp_convex_add_sub_le_update` — the same with `Dᵢ ω = D (update ω i (xs i))`.
-/

open Finset

namespace StatisticalRL.Probability.Stein

namespace Polyhedral

section Sandwich

variable {κ : Type*} [Fintype κ]

/-- `polyPhi` is the explicit `Finset.sup'` expression of `PolyhedralSeparation`. -/
theorem polyPhi_eq_sup' (𝓕 : Finset ((κ → ℝ) × ℝ)) (h𝓕 : 𝓕.Nonempty) (x : κ → ℝ) :
    polyPhi 𝓕 h𝓕 x = 𝓕.sup' h𝓕 (fun q ↦ ∑ j, q.1 j * x j - q.2) := rfl

/-- **Upper sandwich.** If `φ` classifies `w` and `w + d` correctly with respect to `C`, then
`1_C(w + d) ≤ 1_C(w) + 1{0 ≤ φ w ≤ ‖d‖}`. -/
theorem indicator_add_le_indicator_add_intervalInd {𝓕 : Finset ((κ → ℝ) × ℝ)}
    (h𝓕 : 𝓕.Nonempty) (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) {C : Set (κ → ℝ)} {w d : κ → ℝ}
    (hw : polyPhi 𝓕 h𝓕 w ≤ 0 ↔ w ∈ C) (hwd : polyPhi 𝓕 h𝓕 (w + d) ≤ 0 ↔ w + d ∈ C) :
    C.indicator (fun _ ↦ (1 : ℝ)) (w + d) ≤
      C.indicator (fun _ ↦ (1 : ℝ)) w + intervalInd 0 ‖d‖ (polyPhi 𝓕 h𝓕 w) := by
  have hI0 := intervalInd_nonneg 0 ‖d‖ (polyPhi 𝓕 h𝓕 w)
  by_cases h1 : w + d ∈ C
  · by_cases h0 : w ∈ C
    · simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h0]
      linarith
    · have hpos : 0 < polyPhi 𝓕 h𝓕 w := lt_of_not_ge fun h ↦ h0 (hw.1 h)
      have hneg : polyPhi 𝓕 h𝓕 (w + d) ≤ 0 := hwd.2 h1
      have hlip := abs_polyPhi_sub_le h𝓕 h𝓕1 w (w + d)
      rw [show w - (w + d) = -d by abel, norm_neg] at hlip
      have hle : polyPhi 𝓕 h𝓕 w ≤ ‖d‖ := by linarith [(abs_le.1 hlip).2]
      have hI : intervalInd 0 ‖d‖ (polyPhi 𝓕 h𝓕 w) = 1 := by
        unfold intervalInd; rw [if_pos ⟨hpos.le, hle⟩]
      simp only [Set.indicator_of_mem h1, Set.indicator_of_notMem h0, hI]
      norm_num
  · simp only [Set.indicator_of_notMem h1]
    have : 0 ≤ C.indicator (fun _ ↦ (1 : ℝ)) w :=
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) w
    linarith

/-- **Lower sandwich.** If `φ` classifies `w` and `w + d` correctly with respect to `C`, then
`1_C(w) ≤ 1_C(w + d) + 1{-‖d‖ ≤ φ w ≤ 0}`. -/
theorem indicator_le_indicator_add_add_intervalInd {𝓕 : Finset ((κ → ℝ) × ℝ)}
    (h𝓕 : 𝓕.Nonempty) (h𝓕1 : ∀ q ∈ 𝓕, ∑ j, |q.1 j| = 1) {C : Set (κ → ℝ)} {w d : κ → ℝ}
    (hw : polyPhi 𝓕 h𝓕 w ≤ 0 ↔ w ∈ C) (hwd : polyPhi 𝓕 h𝓕 (w + d) ≤ 0 ↔ w + d ∈ C) :
    C.indicator (fun _ ↦ (1 : ℝ)) w ≤
      C.indicator (fun _ ↦ (1 : ℝ)) (w + d) + intervalInd (-‖d‖) 0 (polyPhi 𝓕 h𝓕 w) := by
  have hI0 := intervalInd_nonneg (-‖d‖) 0 (polyPhi 𝓕 h𝓕 w)
  by_cases h0 : w ∈ C
  · by_cases h1 : w + d ∈ C
    · simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h0]
      linarith
    · have hpos : 0 < polyPhi 𝓕 h𝓕 (w + d) := lt_of_not_ge fun h ↦ h1 (hwd.1 h)
      have hneg : polyPhi 𝓕 h𝓕 w ≤ 0 := hw.2 h0
      have hlip := abs_polyPhi_sub_le h𝓕 h𝓕1 w (w + d)
      rw [show w - (w + d) = -d by abel, norm_neg] at hlip
      have hle : -‖d‖ ≤ polyPhi 𝓕 h𝓕 w := by linarith [(abs_le.1 hlip).1]
      have hI : intervalInd (-‖d‖) 0 (polyPhi 𝓕 h𝓕 w) = 1 := by
        unfold intervalInd; rw [if_pos ⟨hle, hneg⟩]
      simp only [Set.indicator_of_mem h0, Set.indicator_of_notMem h1, hI]
      norm_num
  · simp only [Set.indicator_of_notMem h0]
    have : 0 ≤ C.indicator (fun _ ↦ (1 : ℝ)) (w + d) :=
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) (w + d)
    linarith

end Sandwich

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  {κ : Type*} [Fintype κ]

/-- **Nonlinear transfer over convex sets.** Let the summands `ξᵢ` be mean zero and bounded by
`δ` in the sup norm, and let `0 < λ ≤ ∑ᵢ E⟨v, ξᵢ⟩²` for every `v` with `∑ⱼ |vⱼ| = 1`. Let `D` be
any perturbation and `Dᵢ` random vectors not depending on the coordinate `ω i`. Then for every
convex `C` (not necessarily closed or measurable), with `W = vsum ξ` and `m = devSum p ξ`,

`|P(W + D ∈ C) - P(W ∈ C)|
  ≤ λ⁻¹ ((4/3)(E[‖W‖‖D‖] + 2δ E‖W‖ + ∑ᵢ E[‖ξᵢ‖ |‖D‖ - ‖Dᵢ‖|]) + E m)`.

Self-contained variant for bounded summands; not a published theorem. -/
theorem abs_pexp_convex_add_sub_le [Nonempty κ] {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → κ → ℝ}
    (hmean : ∀ i j, ∑ x, p i x * ξ i x j = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbd : ∀ i x, ‖ξ i x‖ ≤ δ) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : ∀ v : κ → ℝ, ∑ j, |v j| = 1 → lam ≤ ∑ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2)
    (D : (∀ i, X i) → κ → ℝ) (Di : ι → (∀ i, X i) → κ → ℝ)
    (hDi : ∀ i ω c, Di i (Function.update ω i c) = Di i ω)
    {C : Set (κ → ℝ)} (hC : Convex ℝ C) :
    |pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω + D ω)) -
        pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω))| ≤
      lam⁻¹ * ((4 / 3) * (pexp p (fun ω ↦ ‖vsum ξ ω‖ * ‖D ω‖) +
          2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) +
          ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * |‖D ω‖ - ‖Di i ω‖|)) +
        pexp p (devSum p ξ)) := by
  haveI : DecidableEq (κ → ℝ) := Classical.decEq _
  obtain ⟨R, hR⟩ : ∃ R, (4 / 3) * (pexp p (fun ω ↦ ‖vsum ξ ω‖ * ‖D ω‖) +
      2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) +
      ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * |‖D ω‖ - ‖Di i ω‖|)) +
    pexp p (devSum p ξ) = R := ⟨_, rfl⟩
  rw [hR]
  have hR0 : 0 ≤ R := by
    have h1 : 0 ≤ pexp p (fun ω ↦ ‖vsum ξ ω‖ * ‖D ω‖) :=
      pexp_nonneg hp0 fun ω ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h2 : 0 ≤ pexp p (fun ω ↦ ‖vsum ξ ω‖) := pexp_nonneg hp0 fun ω ↦ norm_nonneg _
    have h3 : 0 ≤ ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * |‖D ω‖ - ‖Di i ω‖|) :=
      Finset.sum_nonneg fun i _ ↦
        pexp_nonneg hp0 fun ω ↦ mul_nonneg (norm_nonneg _) (abs_nonneg _)
    have h4 : 0 ≤ pexp p (devSum p ξ) := pexp_nonneg hp0 (devSum_nonneg p ξ)
    have h5 : 0 ≤ 2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) :=
      mul_nonneg (mul_nonneg zero_le_two hδ) h2
    rw [← hR]
    exact add_nonneg (mul_nonneg (by norm_num) (add_nonneg (add_nonneg h1 h5) h3)) h4
  let P : Finset (κ → ℝ) := univ.image (vsum ξ) ∪ univ.image (fun ω ↦ vsum ξ ω + D ω)
  have hWP : ∀ ω, vsum ξ ω ∈ P := fun ω ↦
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ ω))
  have hWDP : ∀ ω, vsum ξ ω + D ω ∈ P := fun ω ↦
    Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ω ↦ vsum ξ ω + D ω) (Finset.mem_univ ω))
  by_cases hall : ∀ y ∈ P, y ∈ C
  · -- All relevant points lie in `C`: the two indicators agree pathwise.
    have heq : (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω + D ω)) =
        fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω) := by
      funext ω
      rw [Set.indicator_of_mem (hall _ (hWDP ω)), Set.indicator_of_mem (hall _ (hWP ω))]
    rw [show pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω + D ω)) =
      pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω)) from congrArg (pexp p) heq,
      sub_self, abs_zero]
    exact mul_nonneg (inv_nonneg.2 hlam0.le) hR0
  · push_neg at hall
    obtain ⟨y₀, hy₀P, hy₀C⟩ := hall
    obtain ⟨𝓕, h𝓕, h𝓕1, -, -, hrep⟩ :=
      StatisticalRL.Analysis.PolyhedralSeparation.exists_polyhedral_repr hC P hy₀P hy₀C
    have hrep' : ∀ y ∈ P, (polyPhi 𝓕 h𝓕 y ≤ 0 ↔ y ∈ C) := fun y hy ↦ by
      rw [polyPhi_eq_sup']; exact hrep y hy
    -- Shell bound with endpoints `(0, ‖D‖)` and leave-one-out endpoints `(0, ‖Dᵢ‖)`.
    have hA := pexp_intervalInd_polyhedral_le hp0 hp1 hmean hδ hbd hlam 𝓕 h𝓕 h𝓕1
      (fun _ ↦ 0) (fun ω ↦ ‖D ω‖) (fun ω ↦ norm_nonneg (D ω)) (fun _ _ ↦ 0)
      (fun i ω ↦ ‖Di i ω‖) (fun _ _ _ ↦ rfl) (fun i ω c ↦ by simp only [hDi])
    -- Shell bound with endpoints `(-‖D‖, 0)` and leave-one-out endpoints `(-‖Dᵢ‖, 0)`.
    have hB := pexp_intervalInd_polyhedral_le hp0 hp1 hmean hδ hbd hlam 𝓕 h𝓕 h𝓕1
      (fun ω ↦ -‖D ω‖) (fun _ ↦ 0) (fun ω ↦ by simp) (fun i ω ↦ -‖Di i ω‖)
      (fun _ _ ↦ 0) (fun i ω c ↦ by simp only [hDi]) (fun _ _ _ ↦ rfl)
    have hRA : (4 / 3) * (pexp p (fun ω ↦ ‖vsum ξ ω‖ * (‖D ω‖ - 0)) +
          2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) +
          ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * (|0 - 0| + |‖D ω‖ - ‖Di i ω‖|))) +
        pexp p (devSum p ξ) = R := by
      rw [← hR]; simp only [sub_zero, sub_self, abs_zero, zero_add]
    have hRB : (4 / 3) * (pexp p (fun ω ↦ ‖vsum ξ ω‖ * (0 - -‖D ω‖)) +
          2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) +
          ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ * (|-‖D ω‖ - -‖Di i ω‖| + |0 - 0|))) +
        pexp p (devSum p ξ) = R := by
      have e : ∀ x y : ℝ, |-x - -y| = |x - y| := fun x y ↦ by
        rw [show -x - -y = -(x - y) by ring, abs_neg]
      rw [← hR]; simp only [zero_sub, neg_neg, e, sub_self, abs_zero, add_zero]
    rw [hRA] at hA
    rw [hRB] at hB
    have hA' : pexp p (fun ω ↦ intervalInd 0 ‖D ω‖ (polyPhi 𝓕 h𝓕 (vsum ξ ω))) ≤
        lam⁻¹ * R := by
      rw [inv_mul_eq_div, le_div_iff₀ hlam0, mul_comm]; exact hA
    have hB' : pexp p (fun ω ↦ intervalInd (-‖D ω‖) 0 (polyPhi 𝓕 h𝓕 (vsum ξ ω))) ≤
        lam⁻¹ * R := by
      rw [inv_mul_eq_div, le_div_iff₀ hlam0, mul_comm]; exact hB
    have hup : pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω + D ω)) ≤
        pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω)) +
          pexp p (fun ω ↦ intervalInd 0 ‖D ω‖ (polyPhi 𝓕 h𝓕 (vsum ξ ω))) := by
      rw [← pexp_add]
      exact pexp_mono hp0 fun ω ↦ indicator_add_le_indicator_add_intervalInd h𝓕 h𝓕1
        (hrep' _ (hWP ω)) (hrep' _ (hWDP ω))
    have hlow : pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω)) ≤
        pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω + D ω)) +
          pexp p (fun ω ↦ intervalInd (-‖D ω‖) 0 (polyPhi 𝓕 h𝓕 (vsum ξ ω))) := by
      rw [← pexp_add]
      exact pexp_mono hp0 fun ω ↦ indicator_le_indicator_add_add_intervalInd h𝓕 h𝓕1
        (hrep' _ (hWP ω)) (hrep' _ (hWDP ω))
    rw [abs_sub_le_iff]
    constructor <;> linarith

/-- **Nonlinear transfer over convex sets, replacement form.** As
`abs_pexp_convex_add_sub_le`, with the leave-one-out perturbation
`D⁽ⁱ⁾ ω = D (update ω i (xs i))` for a fixed replacement tuple `xs`. -/
theorem abs_pexp_convex_add_sub_le_update [Nonempty κ] {p : ∀ i, X i → ℝ}
    (hp0 : ∀ i x, 0 ≤ p i x) (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → κ → ℝ}
    (hmean : ∀ i j, ∑ x, p i x * ξ i x j = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbd : ∀ i x, ‖ξ i x‖ ≤ δ) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : ∀ v : κ → ℝ, ∑ j, |v j| = 1 → lam ≤ ∑ i, ∑ x, p i x * (v ⬝ᵥ ξ i x) ^ 2)
    (D : (∀ i, X i) → κ → ℝ) (xs : ∀ i, X i) {C : Set (κ → ℝ)} (hC : Convex ℝ C) :
    |pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω + D ω)) -
        pexp p (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (vsum ξ ω))| ≤
      lam⁻¹ * ((4 / 3) * (pexp p (fun ω ↦ ‖vsum ξ ω‖ * ‖D ω‖) +
          2 * δ * pexp p (fun ω ↦ ‖vsum ξ ω‖) +
          ∑ i, pexp p (fun ω ↦ ‖ξ i (ω i)‖ *
            |‖D ω‖ - ‖D (Function.update ω i (xs i))‖|)) +
        pexp p (devSum p ξ)) :=
  abs_pexp_convex_add_sub_le hp0 hp1 hmean hδ hbd hlam0 hlam D
    (fun i ω ↦ D (Function.update ω i (xs i))) (fun i ω c ↦ by
      simp only [Function.update_idem]) hC

end Transfer

end Polyhedral

end StatisticalRL.Probability.Stein
