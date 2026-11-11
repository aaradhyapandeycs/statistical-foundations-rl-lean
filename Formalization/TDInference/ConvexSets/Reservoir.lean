import Formalization.TDInference.LinearisedCovariance
import Formalization.TDInference.SmoothApproximation
import Formalization.Probability.GaussianConvexShell
import Formalization.Probability.ConvexLindebergReservoirBase
import Mathlib.Algebra.Order.Chebyshev

/-!
# Theorem 7.11, all-convex route: the TD reservoir condition and the Gaussian target

Infrastructure for the all-convex-sets route to `thm:Berry-Esseen-linear`
(`chapters/inference.tex:132–141`; `d_cvx` at :124–127; `Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117, with
`Γ := Γ_true`, SOURCE-ISSUES C43). No source result is claimed here. This module supplies the
TD-specific inputs of the generic reservoir Lindeberg theorem
(`Probability/ConvexLindebergReservoir.lean`): the reservoir condition for the linearised TD
statistic, and the Gaussian target as a linear image of a standard Gaussian with its convex shell
bound. The reservoir threshold uses `ℓ∞ → ℓ∞` operator norms throughout, so no `√S` factor enters
it.

## (a) Reservoir condition for the linearised TD statistic

* `ReservoirCond e L c r₀` (generic; defined in `ConvexLindebergReservoirBase.lean` and consumed
  by the reservoir Lindeberg theorem): for the swap order `e : Fin n ≃ κ`, the summed
  covariances `L (e m) L (e m)ᵀ` of the last `r` swapped indices dominate `(c r / n) I` in the
  Euclidean quadratic form, for every `r₀ ≤ r ≤ n`.
* `exists_reservoirCond_of_good`: if all indices outside a set `B` with `2|B| ≤ n` have covariance
  `≥ λ I`, then swapping `B` first gives `ReservoirCond e L c 1` for every `c` with `2c ≤ λ n`.
* ℓ¹ duality (`sum_abs_vecMul_ge`): if `‖A‖_{∞→∞} ≤ α` and `‖W − A⁻¹‖_{∞→∞} ≤ 1/(2α)`, then
  `‖Wᵀu‖₁ ≥ ‖u‖₁/(2α)`; hence (`quadForm_smul_mul_diagonal_sqrt_ge`) the factor
  `L = c W diag(√Γ)` with `Γ ≥ γ` has `uᵀ L Lᵀ u ≥ c² γ/(4α² S) · uᵀu`. This uses the
  `ℓ∞ → ℓ∞` norms of `norm_linWeight_sub_inv_mulVec_le` directly, with no `√S` in the
  threshold.
* TD instance: `linFactor T k = T^{-1/2} W_k diag(√Γ_true)` with `W_k = linWeight T k`;
  `linFactor_mul_transpose` and `sum_tupleProb_mul_linSummand_mul` identify `L_k L_kᵀ` as the exact
  covariance of the `k`-th summand of `linPart`, and `sum_linFactor_mul_transpose` sums them to
  `linCov`. `sum_abs_tdA_le`: `‖A‖_{∞→∞} ≤ 2`, so the threshold is `θ = 1/4`.
* Markov counting (`card_linBad_le`): with `e_k = linWeightGap` (the coefficient of
  `norm_linWeight_sub_inv_mulVec_le`), `#{k < T : e_k > 1/4} ≤ 4 G T^{2/3}/η₀`, from
  `sum_linWeightGap_le` (`G = linGapConst = 3K_β² + 1/a²`).
* `exists_linFactor_reservoirCond`: for `T ≥ linReservoirBurnIn = ⌈(8G/η₀)³⌉₊` and
  `Γ_true ≥ γmin ≥ 0`, some swap order satisfies `ReservoirCond e (linFactor · T) (γmin/(32 S)) 1`;
  `exists_linFactor_reservoirCond_of_pos`: under `Γ_true ≻ 0` the same with the positive constant
  `min_s Γ_true(s)/(32 S)`.

## (b), (c) The Gaussian target `gaussCov A Γ` as an affine image and its shell bound

* `gaussCov_eq_map_inv_mul_diagonal_sqrt`: `gaussCov A Γ` is the law of `(A⁻¹ diag(√Γ)) Z`, `Z`
  standard Gaussian (an alias of `gaussCov_eq_map_mulVec` in `GaussianCovCompare.lean`, with the
  factor `gaussCovFactor A Γ` written out).
* `inv_mul_diagonal_sqrt_eq`, `isUnit_det_inv_mul_diagonal_sqrt`: for invertible `A` and `Γ > 0`,
  `(A⁻¹ diag(√Γ))⁻¹ = diag(1/√Γ) A`, and the factor is invertible.
* `matrixMaxRowAbsSum_inv_mul_diagonal_sqrt_le`: `‖(A⁻¹ diag √Γ)⁻¹‖_{∞→∞} ≤ ‖A‖_{∞→∞}/√γmin`;
  for TD `matrixMaxRowAbsSum_tdGaussFactor_inv_le` gives `2/√γmin`.
* `gaussCov_convexShell_le`, `gaussCov_frontier_convex_eq_zero`,
  `gaussCov_real_convex_eq_interior`, `gaussCov_real_convex_eq_closure` (from the Gaussian convex
  shell bounds of `GaussianConvexShell.lean`); TD forms `tdGaussCov_convexShell_le` (constant
  `4 S² (2/√γmin) r/√(2π)`) and `tdGaussCov_convexShell_le_diagMin` (`γmin = min_s Γ_true(s)`).
-/

open Finset Matrix MeasureTheory Metric
open scoped BigOperators

namespace StatisticalRL.Probability

variable {ι : Type*} [Fintype ι]

/-- `uᵀ L Lᵀ u = ‖Lᵀ u‖₂²`. -/
theorem dotProduct_mul_transpose_mulVec (L : Matrix ι ι ℝ) (u : ι → ℝ) :
    u ⬝ᵥ ((L * Lᵀ) *ᵥ u) = ∑ j, (u ᵥ* L) j ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
  simp only [dotProduct, sq]

theorem dotProduct_mul_transpose_mulVec_nonneg (L : Matrix ι ι ℝ) (u : ι → ℝ) :
    0 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u) := by
  rw [dotProduct_mul_transpose_mulVec]
  exact sum_nonneg fun j _ ↦ sq_nonneg _

private theorem dotProduct_self_nonneg' (u : ι → ℝ) : 0 ≤ u ⬝ᵥ u := by
  simp only [dotProduct]
  exact sum_nonneg fun i _ ↦ mul_self_nonneg _

/-- A permutation of `Fin n` that lists the indices of `B` first: every position `m ≥ |B|`
carries an index outside `B`. -/
theorem exists_equiv_forall_card_le_not_mem {n : ℕ} (B : Finset (Fin n)) :
    ∃ e : Fin n ≃ Fin n, ∀ m : Fin n, B.card ≤ (m : ℕ) → e m ∉ B := by
  classical
  have hb : B.card ≤ n := by simpa using B.card_le_univ
  let e₀ : {m : Fin n // (m : ℕ) < B.card} ≃ {k : Fin n // k ∈ B} :=
    (Fin.castLEquiv hb).symm.trans B.equivFin.symm
  exact ⟨e₀.extendSubtype, fun m hm ↦ e₀.extendSubtype_not_mem m (not_lt.2 hm)⟩

/-- **Reservoir from good indices.** If every index outside `B` has covariance `≥ λ I` and
`2|B| ≤ n`, then the order "indices of `B` first" satisfies `ReservoirCond e L c 1` for every
`c` with `2c ≤ λ n`. -/
theorem exists_reservoirCond_of_good {n : ℕ} (L : Fin n → Matrix ι ι ℝ) (B : Finset (Fin n))
    (hB : 2 * B.card ≤ n) {lam c : ℝ} (hlam : 0 ≤ lam) (hc : 2 * c ≤ lam * n)
    (hgood : ∀ k ∉ B, ∀ u : ι → ℝ, lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((L k * (L k)ᵀ) *ᵥ u)) :
    ∃ e : Fin n ≃ Fin n, ReservoirCond e L c 1 := by
  obtain ⟨e, he⟩ := exists_equiv_forall_card_le_not_mem B
  refine ⟨e, ?_⟩
  intro r hr1 hrn u
  have hn : 0 < n := by omega
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ : ∃ j : ℕ, n - r ≤ j ∧ B.card ≤ j ∧ r ≤ 2 * (n - j) ∧ j < n := by
    rcases le_total (n - r) B.card with h | h
    · exact ⟨B.card, h, le_rfl, by omega, by omega⟩
    · exact ⟨n - r, le_rfl, h, by omega, by omega⟩
  have huu := dotProduct_self_nonneg' u
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr' : (r : ℝ) ≤ 2 * ((n - j : ℕ) : ℝ) := by exact_mod_cast hj3
  have hcoef : c * r / n ≤ lam * ((n - j : ℕ) : ℝ) := by
    rw [div_le_iff₀ hnR]
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have e1 := mul_le_mul_of_nonneg_right hc hr0
    have e2 := mul_le_mul_of_nonneg_left hr' (mul_nonneg hlam hnR.le)
    linarith
  have hmem : ∀ m ∈ Finset.Ici (⟨j, hj4⟩ : Fin n), j ≤ (m : ℕ) := fun m hm ↦
    Fin.le_iff_val_le_val.1 (Finset.mem_Ici.1 hm)
  calc c * r / n * (u ⬝ᵥ u) ≤ lam * ((n - j : ℕ) : ℝ) * (u ⬝ᵥ u) :=
        mul_le_mul_of_nonneg_right hcoef huu
    _ = ∑ m ∈ Finset.Ici (⟨j, hj4⟩ : Fin n), lam * (u ⬝ᵥ u) := by
        simp only [sum_const, Fin.card_Ici, nsmul_eq_mul]
        ring
    _ ≤ ∑ m ∈ Finset.Ici (⟨j, hj4⟩ : Fin n), u ⬝ᵥ ((L (e m) * (L (e m))ᵀ) *ᵥ u) :=
        sum_le_sum fun m hm ↦ hgood _ (he m (hj2.trans (hmem m hm))) u
    _ ≤ ∑ m ∈ Finset.univ.filter (fun m : Fin n ↦ n - r ≤ (m : ℕ)),
          u ⬝ᵥ ((L (e m) * (L (e m))ᵀ) *ᵥ u) :=
        sum_le_sum_of_subset_of_nonneg
          (fun m hm ↦ mem_filter.2 ⟨mem_univ _, hj1.trans (hmem m hm)⟩)
          (fun m _ _ ↦ dotProduct_mul_transpose_mulVec_nonneg _ u)

/-! ## `ℓ∞`/`ℓ¹` duality for square matrices -/

/-- `‖xᵀ M‖₁ ≤ (max row sum of M) ‖x‖₁`. -/
theorem sum_abs_vecMul_le (M : Matrix ι ι ℝ) {c : ℝ} (h : ∀ i, ∑ j, |M i j| ≤ c)
    (x : ι → ℝ) : ∑ j, |(x ᵥ* M) j| ≤ c * ∑ i, |x i| := by
  calc ∑ j, |(x ᵥ* M) j| ≤ ∑ j, ∑ i, |x i| * |M i j| := by
        refine sum_le_sum fun j _ ↦ ?_
        simp only [vecMul, dotProduct]
        refine (abs_sum_le_sum_abs _ _).trans_eq ?_
        simp only [abs_mul]
    _ = ∑ i, |x i| * ∑ j, |M i j| := by
        rw [sum_comm]
        simp only [mul_sum]
    _ ≤ ∑ i, |x i| * c := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = c * ∑ i, |x i| := by rw [← sum_mul, mul_comm]

variable [DecidableEq ι]

/-- **ℓ¹ lower bound for a perturbed inverse.** If the rows of `A` have absolute sums `≤ α` and the
rows of `W − A⁻¹` have absolute sums `≤ θ ≤ 1/(2α)`, then `‖uᵀ W‖₁ ≥ ‖u‖₁ / (2α)`. -/
theorem sum_abs_vecMul_ge {A W : Matrix ι ι ℝ} (hA : IsUnit A.det) {α θ : ℝ} (hα : 0 < α)
    (hArow : ∀ i, ∑ j, |A i j| ≤ α) (hW : ∀ i, ∑ j, |(W - A⁻¹) i j| ≤ θ)
    (hθ : θ ≤ 1 / (2 * α)) (u : ι → ℝ) :
    (∑ i, |u i|) / (2 * α) ≤ ∑ j, |(u ᵥ* W) j| := by
  have hinv : (u ᵥ* A⁻¹) ᵥ* A = u := by rw [vecMul_vecMul, nonsing_inv_mul A hA, vecMul_one]
  have h1 : ∑ i, |u i| ≤ α * ∑ j, |(u ᵥ* A⁻¹) j| := by
    calc ∑ i, |u i| = ∑ i, |((u ᵥ* A⁻¹) ᵥ* A) i| := by rw [hinv]
      _ ≤ α * ∑ j, |(u ᵥ* A⁻¹) j| := sum_abs_vecMul_le A hArow _
  have h2 : ∑ j, |(u ᵥ* (W - A⁻¹)) j| ≤ θ * ∑ i, |u i| := sum_abs_vecMul_le _ hW u
  have hsplit : u ᵥ* W = u ᵥ* A⁻¹ + u ᵥ* (W - A⁻¹) := by rw [vecMul_sub]; abel
  have h3 : ∑ j, |(u ᵥ* A⁻¹) j| ≤ ∑ j, |(u ᵥ* W) j| + ∑ j, |(u ᵥ* (W - A⁻¹)) j| := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    rw [hsplit, Pi.add_apply]
    have h := abs_add_le ((u ᵥ* A⁻¹) j + (u ᵥ* (W - A⁻¹)) j) (-(u ᵥ* (W - A⁻¹)) j)
    rwa [add_neg_cancel_right, abs_neg] at h
  have hu0 : 0 ≤ ∑ i, |u i| := sum_nonneg fun i _ ↦ abs_nonneg _
  have hα0 : α ≠ 0 := hα.ne'
  have h4 : α * ∑ j, |(u ᵥ* A⁻¹) j| ≤
      α * ∑ j, |(u ᵥ* W) j| + α * ∑ j, |(u ᵥ* (W - A⁻¹)) j| := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left h3 hα.le
  have h5 : α * ∑ j, |(u ᵥ* (W - A⁻¹)) j| ≤ α * (θ * ∑ i, |u i|) :=
    mul_le_mul_of_nonneg_left h2 hα.le
  have h6 : α * (θ * ∑ i, |u i|) ≤ (∑ i, |u i|) / 2 := by
    calc α * (θ * ∑ i, |u i|) ≤ α * (1 / (2 * α) * ∑ i, |u i|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ hu0) hα.le
      _ = (∑ i, |u i|) / 2 := by field_simp
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Quadratic lower bound for a factor `c W diag(√Γ)`** with `W` close to `A⁻¹` (in the sense
of `sum_abs_vecMul_ge`) and `Γ ≥ γ ≥ 0`:
`uᵀ L Lᵀ u ≥ c² γ / (4 α² S) · uᵀ u`, `S = card ι`. -/
theorem quadForm_smul_mul_diagonal_sqrt_ge {A W : Matrix ι ι ℝ} (hA : IsUnit A.det)
    {α θ γ : ℝ} (hα : 0 < α) (hArow : ∀ i, ∑ j, |A i j| ≤ α)
    (hW : ∀ i, ∑ j, |(W - A⁻¹) i j| ≤ θ) (hθ : θ ≤ 1 / (2 * α)) {Γ : ι → ℝ} (hγ : 0 ≤ γ)
    (hΓ : ∀ s, γ ≤ Γ s) (c : ℝ) (u : ι → ℝ) :
    c ^ 2 * γ / (4 * α ^ 2 * Fintype.card ι) * (u ⬝ᵥ u) ≤
      u ⬝ᵥ (((c • (W * diagonal fun s ↦ Real.sqrt (Γ s))) *
        (c • (W * diagonal fun s ↦ Real.sqrt (Γ s)))ᵀ) *ᵥ u) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [dotProduct]
  have hS : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hS0 : (Fintype.card ι : ℝ) ≠ 0 := hS.ne'
  have hentry : ∀ j, (u ᵥ* (c • (W * diagonal fun s ↦ Real.sqrt (Γ s)))) j =
      c * ((u ᵥ* W) j * Real.sqrt (Γ j)) := by
    intro j
    rw [vecMul_smul, ← vecMul_vecMul, Pi.smul_apply, vecMul_diagonal, smul_eq_mul]
  have hsq : ∀ j, (c * ((u ᵥ* W) j * Real.sqrt (Γ j))) ^ 2 =
      c ^ 2 * ((u ᵥ* W) j ^ 2 * Γ j) := by
    intro j
    rw [mul_pow, mul_pow, Real.sq_sqrt (hγ.trans (hΓ j))]
  rw [dotProduct_mul_transpose_mulVec]
  simp_rw [hentry, hsq]
  rw [← mul_sum]
  have hl1 := sum_abs_vecMul_ge hA hα hArow hW hθ u
  have h1 : γ * ∑ j, (u ᵥ* W) j ^ 2 ≤ ∑ j, (u ᵥ* W) j ^ 2 * Γ j := by
    rw [mul_sum]
    refine sum_le_sum fun j _ ↦ ?_
    have := mul_le_mul_of_nonneg_left (hΓ j) (sq_nonneg ((u ᵥ* W) j))
    linarith
  have h2 : (∑ j, |(u ᵥ* W) j|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j, (u ᵥ* W) j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j ↦ |(u ᵥ* W) j|)
    simpa [sq_abs] using this
  have h4 : u ⬝ᵥ u ≤ (∑ i, |u i|) ^ 2 := by
    rw [sq, dotProduct, sum_mul]
    refine sum_le_sum fun i _ ↦ ?_
    rw [← abs_mul_abs_self (u i)]
    exact mul_le_mul_of_nonneg_left
      (single_le_sum (f := fun j ↦ |u j|) (fun j _ ↦ abs_nonneg (u j)) (mem_univ i)) (abs_nonneg _)
  have hu1 : 0 ≤ ∑ i, |u i| := sum_nonneg fun i _ ↦ abs_nonneg _
  have h5 : ((∑ i, |u i|) / (2 * α)) ^ 2 ≤ (∑ j, |(u ᵥ* W) j|) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hu1 (by positivity)) hl1 2
  have h6 : u ⬝ᵥ u / (4 * α ^ 2) ≤ ((∑ i, |u i|) / (2 * α)) ^ 2 := by
    have e : ((∑ i, |u i|) / (2 * α)) ^ 2 = (∑ i, |u i|) ^ 2 / (4 * α ^ 2) := by ring
    rw [e]
    exact div_le_div_of_nonneg_right h4 (by positivity)
  have hq : u ⬝ᵥ u / (4 * α ^ 2) ≤ (Fintype.card ι : ℝ) * ∑ j, (u ᵥ* W) j ^ 2 :=
    h6.trans (h5.trans h2)
  have key : γ / (4 * α ^ 2 * Fintype.card ι) * (u ⬝ᵥ u) ≤ ∑ j, (u ᵥ* W) j ^ 2 * Γ j := by
    calc γ / (4 * α ^ 2 * Fintype.card ι) * (u ⬝ᵥ u) =
          γ * (u ⬝ᵥ u / (4 * α ^ 2)) / Fintype.card ι := by ring
      _ ≤ γ * ((Fintype.card ι : ℝ) * ∑ j, (u ᵥ* W) j ^ 2) / Fintype.card ι :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq hγ) hS.le
      _ = γ * ∑ j, (u ᵥ* W) j ^ 2 := by field_simp
      _ ≤ _ := h1
  calc c ^ 2 * γ / (4 * α ^ 2 * Fintype.card ι) * (u ⬝ᵥ u) =
        c ^ 2 * (γ / (4 * α ^ 2 * Fintype.card ι) * (u ⬝ᵥ u)) := by ring
    _ ≤ c ^ 2 * ∑ j, (u ᵥ* W) j ^ 2 * Γ j := mul_le_mul_of_nonneg_left key (sq_nonneg c)

/-! ## Max row sums and the factor `A⁻¹ diag(√Γ)` -/

/-- `diag(1/√Γ) A` is a left inverse of `A⁻¹ diag(√Γ)`. -/
theorem diagonal_inv_sqrt_mul_mul_eq_one {A : Matrix ι ι ℝ} {Γ : ι → ℝ} (hA : IsUnit A.det)
    (hΓ : ∀ s, 0 < Γ s) :
    (diagonal (fun s ↦ (Real.sqrt (Γ s))⁻¹) * A) * (A⁻¹ * diagonal fun s ↦ Real.sqrt (Γ s)) =
      1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, mul_nonsing_inv A hA, Matrix.one_mul,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext s
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (hΓ s)).ne'

/-- `(A⁻¹ diag(√Γ))⁻¹ = diag(1/√Γ) A` for invertible `A` and `Γ > 0`. -/
theorem inv_mul_diagonal_sqrt_eq {A : Matrix ι ι ℝ} {Γ : ι → ℝ} (hA : IsUnit A.det)
    (hΓ : ∀ s, 0 < Γ s) :
    (A⁻¹ * diagonal fun s ↦ Real.sqrt (Γ s))⁻¹ = diagonal (fun s ↦ (Real.sqrt (Γ s))⁻¹) * A :=
  inv_eq_left_inv (diagonal_inv_sqrt_mul_mul_eq_one hA hΓ)

/-- `A⁻¹ diag(√Γ)` is invertible for invertible `A` and `Γ > 0`. -/
theorem isUnit_det_inv_mul_diagonal_sqrt {A : Matrix ι ι ℝ} {Γ : ι → ℝ} (hA : IsUnit A.det)
    (hΓ : ∀ s, 0 < Γ s) : IsUnit (A⁻¹ * diagonal fun s ↦ Real.sqrt (Γ s)).det :=
  isUnit_det_of_left_inverse (diagonal_inv_sqrt_mul_mul_eq_one hA hΓ)

/-- `‖(A⁻¹ diag √Γ)⁻¹‖_{∞→∞} ≤ α / √γ` when the rows of `A` have absolute sums `≤ α` and
`Γ ≥ γ > 0`. -/
theorem matrixMaxRowAbsSum_inv_mul_diagonal_sqrt_le {A : Matrix ι ι ℝ} {Γ : ι → ℝ}
    (hA : IsUnit A.det) {γ α : ℝ} (hγ0 : 0 < γ) (hΓ : ∀ s, γ ≤ Γ s) (hα : 0 ≤ α)
    (hArow : ∀ i, ∑ j, |A i j| ≤ α) :
    matrixMaxRowAbsSum (A⁻¹ * diagonal fun s ↦ Real.sqrt (Γ s))⁻¹ ≤ α / Real.sqrt γ := by
  have hΓpos : ∀ s, 0 < Γ s := fun s ↦ hγ0.trans_le (hΓ s)
  rw [inv_mul_diagonal_sqrt_eq hA hΓpos]
  refine matrixMaxRowAbsSum_le_of_forall (div_nonneg hα (Real.sqrt_nonneg _)) fun i ↦ ?_
  have hs : 0 < Real.sqrt (Γ i) := Real.sqrt_pos.2 (hΓpos i)
  have hsγ : (Real.sqrt (Γ i))⁻¹ ≤ (Real.sqrt γ)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hγ0) (Real.sqrt_le_sqrt (hΓ i))
  simp only [diagonal_mul]
  calc ∑ j, |(Real.sqrt (Γ i))⁻¹ * A i j| = (Real.sqrt (Γ i))⁻¹ * ∑ j, |A i j| := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [abs_mul, abs_of_pos (inv_pos.2 hs)]
    _ ≤ (Real.sqrt γ)⁻¹ * α :=
        mul_le_mul hsγ (hArow i) (sum_nonneg fun j _ ↦ abs_nonneg _)
          (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ = α / Real.sqrt γ := by ring

end StatisticalRL.Probability

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## (b), (c): `gaussCov` as an image of the standard Gaussian; shell bounds -/

section GaussCov

variable (A : Matrix State State ℝ) (Γ : State → ℝ)

/-- `gaussCov A Γ` is the law of `(A⁻¹ diag(√Γ)) Z` with `Z` standard Gaussian. Deliberate alias
of `gaussCov_eq_map_mulVec` with `gaussCovFactor A Γ = A⁻¹ * diagonal (√Γ)` unfolded. -/
theorem gaussCov_eq_map_inv_mul_diagonal_sqrt :
    gaussCov A Γ =
      (stdGaussianPi State).map fun z ↦ (A⁻¹ * diagonal fun s ↦ Real.sqrt (Γ s)) *ᵥ z :=
  gaussCov_eq_map_mulVec A Γ

variable {A Γ}

/-- **Gaussian convex shell bound for `gaussCov`** (infrastructure). For invertible `A` with
absolute row sums `≤ α` and `Γ ≥ γ > 0`, the `r`-shell of a convex `K` has
`N(0, A⁻¹ diag(Γ) A⁻ᵀ)`-mass at most `4 S² (α/√γ) r / √(2π)`. -/
theorem gaussCov_convexShell_le (hA : IsUnit A.det) {γ α : ℝ} (hγ0 : 0 < γ)
    (hΓ : ∀ s, γ ≤ Γ s) (hα : 0 ≤ α) (hArow : ∀ i, ∑ j, |A i j| ≤ α) {K : Set (State → ℝ)}
    (hK : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r) :
    (gaussCov A Γ).real (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      4 * (Fintype.card State : ℝ) ^ 2 * (α / Real.sqrt γ) * r / Real.sqrt (2 * Real.pi) := by
  have hΓpos : ∀ s, 0 < Γ s := fun s ↦ hγ0.trans_le (hΓ s)
  rw [gaussCov_eq_map_inv_mul_diagonal_sqrt]
  refine (map_mulVec_convexShell_le _ (isUnit_det_inv_mul_diagonal_sqrt hA hΓpos) hK hr).trans ?_
  have hm := matrixMaxRowAbsSum_inv_mul_diagonal_sqrt_le hA hγ0 hΓ hα hArow
  have h4 : (0 : ℝ) ≤ 4 * (Fintype.card State : ℝ) ^ 2 := by positivity
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm h4) hr) (Real.sqrt_nonneg _)

/-- Convex frontiers are `gaussCov`-null (infrastructure). -/
theorem gaussCov_frontier_convex_eq_zero (hA : IsUnit A.det) (hΓ : ∀ s, 0 < Γ s)
    {K : Set (State → ℝ)} (hK : Convex ℝ K) : gaussCov A Γ (frontier K) = 0 := by
  rw [gaussCov_eq_map_inv_mul_diagonal_sqrt]
  exact map_mulVec_frontier_convex_eq_zero _ (isUnit_det_inv_mul_diagonal_sqrt hA hΓ) hK

/-- The `gaussCov`-mass of any convex set (measurable or not) equals that of its interior. -/
theorem gaussCov_real_convex_eq_interior (hA : IsUnit A.det) (hΓ : ∀ s, 0 < Γ s)
    {K : Set (State → ℝ)} (hK : Convex ℝ K) :
    (gaussCov A Γ).real K = (gaussCov A Γ).real (interior K) := by
  rw [gaussCov_eq_map_inv_mul_diagonal_sqrt]
  exact map_mulVec_real_convex_eq_interior _ (isUnit_det_inv_mul_diagonal_sqrt hA hΓ) hK

/-- The `gaussCov`-mass of any convex set (measurable or not) equals that of its closure. -/
theorem gaussCov_real_convex_eq_closure (hA : IsUnit A.det) (hΓ : ∀ s, 0 < Γ s)
    {K : Set (State → ℝ)} (hK : Convex ℝ K) :
    (gaussCov A Γ).real K = (gaussCov A Γ).real (closure K) := by
  rw [gaussCov_eq_map_inv_mul_diagonal_sqrt]
  exact map_mulVec_real_convex_eq_closure _ (isUnit_det_inv_mul_diagonal_sqrt hA hΓ) hK

end GaussCov

/-! ### TD specialisation: `A = tdA`, `Γ = Γ_true` -/

/-- `‖A‖_{∞→∞} ≤ 2` for `A = diag(μ)(I − γP_π)`: row `s` has absolute sum `≤ μ(s)(1 + γ)`. -/
theorem sum_abs_tdA_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) : ∑ s', |tdA M π μ s s'| ≤ 2 := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hμ0 := μ.prob_nonneg s
  have hμ1 := prob_le_one μ s
  have hrow : ∀ s', |tdA M π μ s s'| ≤ μ.prob s *
      ((1 : Matrix State State ℝ) s s' + M.discount * (M.policyTransition π s).prob s') := by
    intro s'
    have hP := (M.policyTransition π s).prob_nonneg s'
    have hI : 0 ≤ (1 : Matrix State State ℝ) s s' := by
      rw [Matrix.one_apply]; split_ifs <;> norm_num
    have hγP := mul_nonneg hγ0 hP
    have he : tdA M π μ s s' = μ.prob s *
        ((1 : Matrix State State ℝ) s s' - M.discount * (M.policyTransition π s).prob s') := by
      simp only [tdA, diagonal_mul, Matrix.sub_apply, Matrix.smul_apply, policyMatrix,
        Matrix.of_apply, smul_eq_mul]
    rw [he, abs_mul, abs_of_nonneg hμ0]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hμ0
  have h1sum : ∑ s', (1 : Matrix State State ℝ) s s' = 1 := by simp [Matrix.one_apply]
  calc ∑ s', |tdA M π μ s s'| ≤ ∑ s', μ.prob s *
        ((1 : Matrix State State ℝ) s s' + M.discount * (M.policyTransition π s).prob s') :=
        sum_le_sum fun s' _ ↦ hrow s'
    _ = μ.prob s * (1 + M.discount) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, (M.policyTransition π s).sum_prob, mul_one,
          h1sum]
    _ ≤ 2 := by nlinarith

/-- `gaussCov A Γ_true` is the law of `tdGaussFactor Z = A⁻¹ diag(√Γ_true) Z`. -/
theorem gaussCov_tdA_eq_map (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) :
    gaussCov (tdA M π μ) (trueGamma M π μ) =
      (stdGaussianPi State).map fun z ↦ tdGaussFactor M π μ *ᵥ z :=
  gaussCov_eq_map_inv_mul_diagonal_sqrt _ _

/-- `tdGaussFactor = A⁻¹ diag(√Γ_true)` is invertible when `μ > 0` and `Γ_true > 0`. -/
theorem isUnit_det_tdGaussFactor (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    IsUnit (tdGaussFactor M π μ).det :=
  isUnit_det_inv_mul_diagonal_sqrt
    ((Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)) hΓ

/-- `‖tdGaussFactor⁻¹‖_{∞→∞} ≤ 2/√γmin` when `Γ_true ≥ γmin > 0`. -/
theorem matrixMaxRowAbsSum_tdGaussFactor_inv_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin γmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hγ0 : 0 < γmin)
    (hγ : ∀ s, γmin ≤ trueGamma M π μ s) :
    matrixMaxRowAbsSum (tdGaussFactor M π μ)⁻¹ ≤ 2 / Real.sqrt γmin :=
  matrixMaxRowAbsSum_inv_mul_diagonal_sqrt_le
    ((Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)) hγ0 hγ zero_le_two
    (sum_abs_tdA_le M π μ)

/-- **Gaussian convex shell bound for the TD target** `N(0, A⁻¹ Γ_true A⁻ᵀ)` (infrastructure):
mass `≤ 4 S² (2/√γmin) r / √(2π)` when `Γ_true ≥ γmin > 0`. -/
theorem tdGaussCov_convexShell_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin γmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hγ0 : 0 < γmin)
    (hγ : ∀ s, γmin ≤ trueGamma M π μ s) {K : Set (State → ℝ)} (hK : Convex ℝ K) {r : ℝ}
    (hr : 0 ≤ r) :
    (gaussCov (tdA M π μ) (trueGamma M π μ)).real
        (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      4 * (Fintype.card State : ℝ) ^ 2 * (2 / Real.sqrt γmin) * r /
        Real.sqrt (2 * Real.pi) :=
  gaussCov_convexShell_le ((Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin))
    hγ0 hγ zero_le_two (sum_abs_tdA_le M π μ) hK hr

/-- `tdGaussCov_convexShell_le` with `γmin = min_s Γ_true(s)` (`diagMin`). -/
theorem tdGaussCov_convexShell_le_diagMin [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s)
    {K : Set (State → ℝ)} (hK : Convex ℝ K) {r : ℝ} (hr : 0 ≤ r) :
    (gaussCov (tdA M π μ) (trueGamma M π μ)).real
        (cthickening r K ∩ cthickening r (interior K)ᶜ) ≤
      4 * (Fintype.card State : ℝ) ^ 2 * (2 / Real.sqrt (diagMin (trueGamma M π μ))) * r /
        Real.sqrt (2 * Real.pi) :=
  tdGaussCov_convexShell_le M π μ hμmin0 hμmin
    ((Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)) hK hr

/-- Convex frontiers are null for the TD target `gaussCov A Γ_true` when `Γ_true > 0`. -/
theorem tdGaussCov_frontier_convex_eq_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s)
    {K : Set (State → ℝ)} (hK : Convex ℝ K) :
    gaussCov (tdA M π μ) (trueGamma M π μ) (frontier K) = 0 :=
  gaussCov_frontier_convex_eq_zero
    ((Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)) hΓ hK

/-! ## (a): the reservoir condition for the linearised TD statistic -/

/-- The covariance factor `L_k = T^{-1/2} W_k diag(√Γ_true)` of the `k`-th summand of `linPart`,
`W_k = linWeight T k`. -/
noncomputable def linFactor (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ) : Matrix State State ℝ :=
  (Real.sqrt T)⁻¹ • (linWeight M π μ η₀ T k * diagonal fun s ↦ Real.sqrt (trueGamma M π μ s))

theorem inv_sqrt_mul_inv_sqrt_natCast (T : ℕ) :
    (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- `L_k L_kᵀ = T⁻¹ W_k diag(Γ_true) W_kᵀ`, the `k`-th term of `linCov`. -/
theorem linFactor_mul_transpose (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ) :
    linFactor M π μ η₀ T k * (linFactor M π μ η₀ T k)ᵀ =
      (T : ℝ)⁻¹ • (linWeight M π μ η₀ T k * diagonal (trueGamma M π μ) *
        (linWeight M π μ η₀ T k)ᵀ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [linFactor, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_diagonal,
    smul_eq_mul]
  have hg := Real.mul_self_sqrt (trueGamma_nonneg M π μ u)
  rw [← inv_sqrt_mul_inv_sqrt_natCast T]
  conv_rhs => rw [← hg]
  ring

/-- `∑_{k<T} L_k L_kᵀ = Λ_T` (`linCov`). -/
theorem sum_linFactor_mul_transpose (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ) :
    ∑ k ∈ range T, linFactor M π μ η₀ T k * (linFactor M π μ η₀ T k)ᵀ = linCov M π μ η₀ T := by
  simp_rw [linFactor_mul_transpose]
  rw [linCov, smul_sum]

/-- **Summand covariance.** `E_x[Y_k(x)_s Y_k(x)_{s'}] = (L_k L_kᵀ)_{s s'}` for the `k`-th
summand `Y_k = linSummand T k` of `linPart` (the `hcov` input of the reservoir Lindeberg theorem, entrywise). -/
theorem sum_tupleProb_mul_linSummand_mul (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ)
    (s s' : State) :
    ∑ x, tupleProb M π μ x * (linSummand M π μ η₀ T k x s * linSummand M π μ η₀ T k x s') =
      (linFactor M π μ η₀ T k * (linFactor M π μ η₀ T k)ᵀ) s s' := by
  rw [linFactor_mul_transpose]
  simp_rw [linSummand_apply]
  have hT := inv_sqrt_mul_inv_sqrt_natCast T
  calc ∑ x, tupleProb M π μ x *
        (-((Real.sqrt T)⁻¹ * ∑ u, linWeight M π μ η₀ T k s u * noiseVec M π x u) *
          -((Real.sqrt T)⁻¹ * ∑ u, linWeight M π μ η₀ T k s' u * noiseVec M π x u)) =
        (T : ℝ)⁻¹ * ∑ x, tupleProb M π μ x *
          ((∑ u, linWeight M π μ η₀ T k s u * noiseVec M π x u) *
            (∑ u, linWeight M π μ η₀ T k s' u * noiseVec M π x u)) := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [← hT]
        ring
    _ = (T : ℝ)⁻¹ * ∑ u, linWeight M π μ η₀ T k s u * linWeight M π μ η₀ T k s' u *
          trueGamma M π μ u := by
        rw [sum_tupleProb_mul_sum_noiseVec_mul]
    _ = _ := by
        rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
        congr 1
        refine sum_congr rfl fun u _ ↦ ?_
        rw [Matrix.mul_diagonal, Matrix.transpose_apply]
        ring

/-- The gap coefficient `e_k = τ_k + p_{k+1,T+1}/a` of `norm_linWeight_sub_inv_mulVec_le`:
`‖(W_k − A⁻¹) v‖_∞ ≤ e_k ‖v‖_∞`. -/
noncomputable def linWeightGap (M : DiscountedMDP State Action) (μmin η₀ : ℝ) (T k : ℕ) : ℝ :=
  contrDrift (linRate M μmin) (linStepSeq η₀) T k +
    contrProd (linRate M μmin) (linStepSeq η₀) (k + 1) (T + 1) / linRate M μmin

/-- The constant `G = 3K_β² + 1/a²` of `sum_linWeightGap_le`. -/
noncomputable def linGapConst (M : DiscountedMDP State Action) (μmin η₀ : ℝ) : ℝ :=
  3 * linWeightConst M μmin η₀ ^ 2 + 1 / linRate M μmin ^ 2

/-- The burn-in `T₀ = ⌈(8G/η₀)³⌉₊` after which at most half of the weights are bad. -/
noncomputable def linReservoirBurnIn (M : DiscountedMDP State Action) (μmin η₀ : ℝ) : ℕ :=
  ⌈(8 * linGapConst M μmin η₀ / η₀) ^ 3⌉₊

omit [DecidableEq State] in
theorem linWeightGap_nonneg (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) (T k : ℕ) : 0 ≤ linWeightGap M μmin η₀ T k :=
  add_nonneg (contrDrift_linStepSeq_nonneg (M := M) h0.le hμmin0 hμmin h1 T k)
      (div_nonneg (contrProd_nonneg
        (fun i ↦ linRate_mul_stepSize_le M μ hμmin0 hμmin h0.le h1 i) _ _) (linRate_pos M hμmin0).le)

omit [DecidableEq State] in
theorem linGapConst_pos (M : DiscountedMDP State Action) {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) :
    0 < linGapConst M μmin η₀ := by
  have := linRate_pos M hμmin0
  unfold linGapConst
  positivity

/-- Row sums of `W_k − A⁻¹` are at most `e_k` (for `k ≤ T`). -/
theorem sum_abs_linWeight_sub_inv_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    {k T : ℕ} (hkT : k ≤ T) (i : State) :
    ∑ j, |(linWeight M π μ η₀ T k - (tdA M π μ)⁻¹) i j| ≤ linWeightGap M μmin η₀ T k :=
  StatisticalRL.Analysis.sum_abs_le_of_norm_mulVec_le _
    (linWeightGap_nonneg M μ h0 h1 hμmin0 hμmin T k)
    (fun v ↦ norm_linWeight_sub_inv_mulVec_le M π μ h0 h1 hμmin0 hμmin hkT v) i

/-- **Good weights have a non-degenerate covariance.** If `k ≤ T`, `e_k ≤ 1/4` and
`Γ_true ≥ γmin ≥ 0`, then `uᵀ L_k L_kᵀ u ≥ γmin / (16 S T) · uᵀu`. -/
theorem linFactor_quadForm_ge (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin γmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (hγ0 : 0 ≤ γmin) (hγ : ∀ s, γmin ≤ trueGamma M π μ s) {k T : ℕ} (hkT : k ≤ T)
    (hgood : linWeightGap M μmin η₀ T k ≤ 1 / 4) (u : State → ℝ) :
    γmin / (16 * Fintype.card State * T) * (u ⬝ᵥ u) ≤
      u ⬝ᵥ ((linFactor M π μ η₀ T k * (linFactor M π μ η₀ T k)ᵀ) *ᵥ u) := by
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  have h := quadForm_smul_mul_diagonal_sqrt_ge hA two_pos (sum_abs_tdA_le M π μ)
    (sum_abs_linWeight_sub_inv_le M π μ h0 h1 hμmin0 hμmin hkT)
    (by rw [show (1 : ℝ) / (2 * 2) = 1 / 4 by norm_num]; exact hgood) hγ0 hγ (Real.sqrt T)⁻¹ u
  have hc : (Real.sqrt T)⁻¹ ^ 2 = (T : ℝ)⁻¹ := by
    rw [sq, inv_sqrt_mul_inv_sqrt_natCast]
  calc γmin / (16 * Fintype.card State * T) * (u ⬝ᵥ u) =
        (Real.sqrt T)⁻¹ ^ 2 * γmin / (4 * 2 ^ 2 * Fintype.card State) * (u ⬝ᵥ u) := by
        rw [hc]; ring
    _ ≤ _ := h

omit [DecidableEq State] in
/-- **Markov counting.** At most `4 G T^{2/3} / η₀` of the weights `W_k`, `k < T`, are bad
(`e_k > 1/4`). -/
theorem card_linBad_le (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {T : ℕ} (hT : 1 ≤ T) :
    ((Finset.univ.filter fun k : Fin T ↦ 1 / 4 < linWeightGap M μmin η₀ T k).card : ℝ) ≤
      4 * linGapConst M μmin η₀ * natCubeRoot T ^ 2 / η₀ := by
  set B := Finset.univ.filter fun k : Fin T ↦ 1 / 4 < linWeightGap M μmin η₀ T k
  have hsum : ∑ k ∈ range T, linWeightGap M μmin η₀ T k ≤
      linGapConst M μmin η₀ * natCubeRoot T ^ 2 / η₀ :=
    sum_linWeightGap_le M μ hμmin0 hμmin h0 h1 hT
  have hB1 : (B.card : ℝ) * (1 / 4) ≤ ∑ k ∈ B, linWeightGap M μmin η₀ T k := by
    calc (B.card : ℝ) * (1 / 4) = ∑ k ∈ B, (1 / 4 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ B, linWeightGap M μmin η₀ T k :=
          sum_le_sum fun k hk ↦ (mem_filter.1 hk).2.le
  have hB2 : ∑ k ∈ B, linWeightGap M μmin η₀ T k ≤
      ∑ k : Fin T, linWeightGap M μmin η₀ T k :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun k _ _ ↦ linWeightGap_nonneg M μ h0 h1 hμmin0 hμmin T k
  have hB3 : ∑ k : Fin T, linWeightGap M μmin η₀ T k =
      ∑ k ∈ range T, linWeightGap M μmin η₀ T k :=
    Fin.sum_univ_eq_sum_range (fun k ↦ linWeightGap M μmin η₀ T k) T
  have e : 4 * linGapConst M μmin η₀ * natCubeRoot T ^ 2 / η₀ =
      4 * (linGapConst M μmin η₀ * natCubeRoot T ^ 2 / η₀) := by ring
  rw [e]
  linarith

omit [DecidableEq State] in
theorem one_le_linReservoirBurnIn (M : DiscountedMDP State Action) {μmin η₀ : ℝ}
    (hμmin0 : 0 < μmin) (h0 : 0 < η₀) : 1 ≤ linReservoirBurnIn M μmin η₀ := by
  have := linGapConst_pos M (η₀ := η₀) hμmin0
  exact Nat.ceil_pos.2 (by positivity)

omit [DecidableEq State] in
/-- After the burn-in, at most half of the weights are bad: `2 |B| ≤ T`. -/
theorem two_mul_card_linBad_le (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {T : ℕ} (hT : linReservoirBurnIn M μmin η₀ ≤ T) :
    2 * (Finset.univ.filter fun k : Fin T ↦ 1 / 4 < linWeightGap M μmin η₀ T k).card ≤ T := by
  have hT1 : 1 ≤ T := (one_le_linReservoirBurnIn M hμmin0 h0).trans hT
  have hG := (linGapConst_pos M (η₀ := η₀) hμmin0).le
  have hc := card_linBad_le M μ hμmin0 hμmin h0 h1 hT1
  set u := natCubeRoot T
  have hu3 : u ^ 3 = (T : ℝ) := natCubeRoot_cube T
  have hu0 : 0 ≤ u := natCubeRoot_nonneg T
  have hge : 8 * linGapConst M μmin η₀ / η₀ ≤ u := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hu0 ?_
    rw [hu3]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hT)
  have hle : 4 * linGapConst M μmin η₀ * u ^ 2 / η₀ ≤ (T : ℝ) / 2 := by
    rw [← hu3]
    calc 4 * linGapConst M μmin η₀ * u ^ 2 / η₀ =
          8 * linGapConst M μmin η₀ / η₀ * u ^ 2 / 2 := by ring
      _ ≤ u * u ^ 2 / 2 := by gcongr
      _ = u ^ 3 / 2 := by ring
  have : (2 * (Finset.univ.filter fun k : Fin T ↦ 1 / 4 < linWeightGap M μmin η₀ T k).card : ℝ)
      ≤ T := by linarith
  exact_mod_cast this

/-- **TD reservoir condition**. For `0 < η₀ ≤ 1`,
`0 < μmin ≤ μ(s)`, `Γ_true ≥ γmin ≥ 0` and `T ≥ linReservoirBurnIn`, swapping the bad weights
(`e_k > 1/4`) first gives a swap order with
`ReservoirCond e (k ↦ L_k) (γmin / (32 S)) 1`, `L_k = linFactor T k`, `S = |State|`. -/
theorem exists_linFactor_reservoirCond (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin γmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (hγ0 : 0 ≤ γmin) (hγ : ∀ s, γmin ≤ trueGamma M π μ s) {T : ℕ}
    (hT : linReservoirBurnIn M μmin η₀ ≤ T) :
    ∃ e : Fin T ≃ Fin T, ReservoirCond e (fun k : Fin T ↦ linFactor M π μ η₀ T k)
      (γmin / (32 * Fintype.card State)) 1 := by
  have hT1 : 1 ≤ T := (one_le_linReservoirBurnIn M hμmin0 h0).trans hT
  have hTne : (T : ℝ) ≠ 0 := by
    have : (0 : ℝ) < T := by exact_mod_cast hT1
    exact this.ne'
  refine exists_reservoirCond_of_good (fun k : Fin T ↦ linFactor M π μ η₀ T k)
    (Finset.univ.filter fun k : Fin T ↦ 1 / 4 < linWeightGap M μmin η₀ T k)
    (two_mul_card_linBad_le M μ hμmin0 hμmin h0 h1 hT)
    (lam := γmin / (16 * Fintype.card State * T)) (by positivity) ?_ ?_
  · rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hTne]
    exact le_of_eq (by ring)
  · intro k hk u
    have hk' : ¬ (1 / 4 < linWeightGap M μmin η₀ T k) := fun h ↦ hk (mem_filter.2 ⟨mem_univ _, h⟩)
    exact linFactor_quadForm_ge M π μ h0 h1 hμmin0 hμmin hγ0 hγ k.isLt.le (not_lt.1 hk') u

/-- **TD reservoir condition with a positive constant** (the form the TD consumer uses: the
reservoir Lindeberg theorem needs `0 < c`). If `Γ_true ≻ 0` (all `Γ_true(s) > 0`), the constant `c = min_s Γ_true(s) / (32 S)` is
positive and, for `T ≥ linReservoirBurnIn`, some swap order satisfies `ReservoirCond e L c 1`. -/
theorem exists_linFactor_reservoirCond_of_pos [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) {T : ℕ} (hT : linReservoirBurnIn M μmin η₀ ≤ T) :
    0 < diagMin (trueGamma M π μ) / (32 * Fintype.card State) ∧
      ∃ e : Fin T ≃ Fin T, ReservoirCond e (fun k : Fin T ↦ linFactor M π μ η₀ T k)
        (diagMin (trueGamma M π μ) / (32 * Fintype.card State)) 1 := by
  have hmin : 0 < diagMin (trueGamma M π μ) := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hS : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  exact ⟨by positivity, exists_linFactor_reservoirCond M π μ h0 h1 hμmin0 hμmin hmin.le
    (fun s ↦ Finset.inf'_le _ (mem_univ s)) hT⟩

end StatisticalRL.Ch7Rest.TDInference
