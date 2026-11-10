import Formalization.Probability.StdGaussianPi
import Formalization.TDInference.Definitions
import Formalization.TDInference.SmoothApproximation
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.Matrix.Order

/-!
# Gaussian law identity (milestone M4.1 of the all-convex Theorem 7.11 route)

For matrices `R : Matrix ι κ ℝ` and `Q : Matrix ι κ' ℝ` (rectangular, with possibly different
column index types) with `R Rᵀ = Q Qᵀ`, the image laws of standard Gaussians agree:
`(stdGaussianPi κ).map (R *ᵥ ·) = (stdGaussianPi κ').map (Q *ᵥ ·)`
(`map_mulVec_stdGaussianPi_eq`). In other words, the law of `R Z` depends only on `R Rᵀ`: it is
the centred Gaussian `N(0, R Rᵀ)`.

Route: `ι → ℝ` carries the sup norm (not an inner product space), so we use the Banach-space
characteristic function `charFunDual`:
* `charFunDual_gaussianReal_zero_one`: `φ_{N(0,1)}(L) = exp(-(L 1)²/2)`;
* `charFunDual_stdGaussianPi`: by `charFunDual_pi`, `φ(L) = exp(-∑_j L(e_j)²/2)`;
* `charFunDual_map_mulVec_stdGaussianPi`: by `charFunDual_map`, the image law has
  `φ(L) = exp(-aᵀ (R Rᵀ) a / 2)` with `a i = L(e_i)` (`dualVec`);
* `Measure.ext_of_charFunDual` concludes.

Consumers:
* `exists_mul_transpose_eq_of_posSemidef`: every real PSD matrix has a square factor `Q Qᵀ = S`;
* `gaussCov_eq_map_mulVec`: the repo's `gaussCov A Γ` (law of `A⁻¹(√Γ ⊙ Z)`) is the image law of
  `Z` under the square matrix `A⁻¹ * diagonal (√Γ)`, hence (`gaussCov_eq_map_mulVec_of_mul_transpose`)
  equals `(stdGaussianPi State).map (Q *ᵥ ·)` for any factor `Q` (any column type) with
  `Q Qᵀ = A⁻¹ diag(Γ) A⁻ᵀ`, when `Γ ≥ 0`.

Infrastructure only: this file proves no source result by itself.
-/

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped Matrix

namespace StatisticalRL.Probability

variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']

/-! ## Characteristic functions -/

/-- The characteristic function of `N(0,1)` at a dual vector `L : ℝ →L[ℝ] ℝ`. -/
theorem charFunDual_gaussianReal_zero_one (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = cexp (-((L 1 : ℝ) : ℂ) ^ 2 / 2) := by
  have h : ∀ x : ℝ, L x = L 1 * x := fun x ↦ by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have h' : ∀ x : ℝ, cexp ((L x : ℂ) * I) = cexp ((L 1 : ℂ) * (x : ℂ) * I) := fun x ↦ by
    rw [h x]; push_cast; ring_nf
  rw [charFunDual_apply]
  simp_rw [h']
  rw [← charFun_apply_real, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- The coordinate vector of a dual vector on `ι → ℝ`: `dualVec L i = L (e_i)`. -/
noncomputable def dualVec [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) : ι → ℝ :=
  fun i ↦ L (Pi.single i 1)

/-- A dual vector on `ι → ℝ` is the dot product with its coordinate vector. -/
theorem dual_apply_eq_dotProduct [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = x ⬝ᵥ dualVec L := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs : (Pi.single i (x i) : ι → ℝ) = x i • (Pi.single i 1 : ι → ℝ) := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [hs, map_smul, smul_eq_mul, dualVec]

/-- The characteristic function of the standard Gaussian on `ι → ℝ`. -/
theorem charFunDual_stdGaussianPi [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (stdGaussianPi ι) L =
      cexp (-(((dualVec L ⬝ᵥ dualVec L : ℝ)) : ℂ) / 2) := by
  show charFunDual (Measure.pi fun _ : ι ↦ gaussianReal 0 1) L = _
  rw [charFunDual_pi]
  simp_rw [charFunDual_gaussianReal_zero_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [ContinuousLinearMap.comp_apply, dotProduct, dualVec]
  push_cast
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [sq, neg_div]

/-- `R *ᵥ ·` as a continuous linear map. -/
noncomputable def mulVecCLM (R : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)

omit [Fintype ι] in
@[simp]
theorem coe_mulVecCLM (R : Matrix ι κ ℝ) : ⇑(mulVecCLM R) = (R *ᵥ ·) := by
  ext v i
  simp [mulVecCLM]

theorem measurable_mulVec (R : Matrix ι κ ℝ) : Measurable (R *ᵥ · : (κ → ℝ) → ι → ℝ) := by
  rw [← coe_mulVecCLM]
  exact (mulVecCLM R).continuous.measurable

instance isProbabilityMeasure_map_mulVec_stdGaussianPi (R : Matrix ι κ ℝ) :
    IsProbabilityMeasure ((stdGaussianPi κ).map (R *ᵥ ·)) :=
  Measure.isProbabilityMeasure_map (measurable_mulVec R).aemeasurable

/-- `∑_j L(R e_j)² = aᵀ (R Rᵀ) a` with `a = dualVec L`. -/
theorem dualVec_comp_mulVecCLM [DecidableEq ι] [DecidableEq κ] (R : Matrix ι κ ℝ)
    (L : StrongDual ℝ (ι → ℝ)) :
    dualVec (L.comp (mulVecCLM R)) ⬝ᵥ dualVec (L.comp (mulVecCLM R)) =
      dualVec L ⬝ᵥ ((R * Rᵀ) *ᵥ dualVec L) := by
  have hv : dualVec (L.comp (mulVecCLM R)) = Rᵀ *ᵥ dualVec L := by
    ext j
    simp only [dualVec, ContinuousLinearMap.comp_apply, coe_mulVecCLM]
    rw [dual_apply_eq_dotProduct, mulVec_single_one]
    simp [mulVec, dotProduct, Matrix.col, dualVec]
  rw [hv, ← mulVec_mulVec, dotProduct_mulVec (dualVec L) R, ← mulVec_transpose R]

/-- The characteristic function of `R Z`, `Z` standard Gaussian: `exp(-aᵀ (R Rᵀ) a / 2)`. -/
theorem charFunDual_map_mulVec_stdGaussianPi [DecidableEq ι] (R : Matrix ι κ ℝ)
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual ((stdGaussianPi κ).map (R *ᵥ ·)) L =
      cexp (-(((dualVec L ⬝ᵥ ((R * Rᵀ) *ᵥ dualVec L) : ℝ)) : ℂ) / 2) := by
  classical
  rw [← coe_mulVecCLM, charFunDual_map, charFunDual_stdGaussianPi, dualVec_comp_mulVecCLM]

/-! ## The law identity -/

/-- **M4.1.** The law of `R Z` (`Z` standard Gaussian) depends only on `R Rᵀ`: if
`R Rᵀ = Q Qᵀ` then `R Z` and `Q Z'` have the same law, for any column index types. -/
theorem map_mulVec_stdGaussianPi_eq (R : Matrix ι κ ℝ) (Q : Matrix ι κ' ℝ)
    (h : R * Rᵀ = Q * Qᵀ) :
    (stdGaussianPi κ).map (R *ᵥ ·) = (stdGaussianPi κ').map (Q *ᵥ ·) := by
  classical
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map_mulVec_stdGaussianPi, charFunDual_map_mulVec_stdGaussianPi, h]

/-- Every real positive semidefinite matrix has a square factor `Q Qᵀ = S`. -/
theorem exists_mul_transpose_eq_of_posSemidef {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∃ Q : Matrix ι ι ℝ, Q * Qᵀ = S := by
  classical
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι ι ℝ, S = star B * B :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hS)
  refine ⟨Bᵀ, ?_⟩
  rw [hB, transpose_transpose, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- For a PSD target covariance `S`, the image law under any factor of `S` is the image law
under a fixed square factor. -/
theorem exists_square_factor_map_eq {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∃ Q : Matrix ι ι ℝ, Q * Qᵀ = S ∧ ∀ (R : Matrix ι κ ℝ), R * Rᵀ = S →
      (stdGaussianPi κ).map (R *ᵥ ·) = (stdGaussianPi ι).map (Q *ᵥ ·) := by
  obtain ⟨Q, hQ⟩ := exists_mul_transpose_eq_of_posSemidef hS
  exact ⟨Q, hQ, fun R hR ↦ map_mulVec_stdGaussianPi_eq R Q (hR.trans hQ.symm)⟩

/-! ## Identification of `gaussCov` -/

section GaussCov

open StatisticalRL.Ch7Rest.TDInference

variable {State : Type} [Fintype State] [DecidableEq State]

/-- The square factor of `gaussCov A Γ`: `A⁻¹ * diag(√Γ)`. -/
noncomputable def gaussCovFactor (A : Matrix State State ℝ) (Γ : State → ℝ) :
    Matrix State State ℝ :=
  A⁻¹ * diagonal fun s ↦ Real.sqrt (Γ s)

theorem gaussMap_eq_gaussCovFactor_mulVec (A : Matrix State State ℝ) (Γ : State → ℝ) :
    gaussMap A Γ = (gaussCovFactor A Γ *ᵥ ·) := by
  funext z
  rw [gaussMap, gaussCovFactor, ← mulVec_mulVec]
  congr 1
  funext s
  rw [mulVec_diagonal]

/-- `gaussCov A Γ` is the image of the standard Gaussian under the square matrix
`A⁻¹ * diag(√Γ)`. -/
theorem gaussCov_eq_map_mulVec (A : Matrix State State ℝ) (Γ : State → ℝ) :
    gaussCov A Γ = (stdGaussianPi State).map (gaussCovFactor A Γ *ᵥ ·) := by
  rw [gaussCov, gaussMap_eq_gaussCovFactor_mulVec]

/-- For `Γ ≥ 0`, the factor's Gram matrix is `A⁻¹ diag(Γ) A⁻ᵀ`. -/
theorem gaussCovFactor_mul_transpose (A : Matrix State State ℝ) {Γ : State → ℝ}
    (hΓ : ∀ s, 0 ≤ Γ s) :
    gaussCovFactor A Γ * (gaussCovFactor A Γ)ᵀ = A⁻¹ * diagonal Γ * (A⁻¹)ᵀ := by
  rw [gaussCovFactor, transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc
    (diagonal _), diagonal_mul_diagonal, Matrix.mul_assoc]
  congr 3
  funext s
  exact Real.mul_self_sqrt (hΓ s)

/-- **`gaussCov` as a covariance-determined law.** For `Γ ≥ 0` and any matrix `Q` (any column
type) with `Q Qᵀ = A⁻¹ diag(Γ) A⁻ᵀ`, `gaussCov A Γ` is the law of `Q Z`. -/
theorem gaussCov_eq_map_mulVec_of_mul_transpose (A : Matrix State State ℝ) {Γ : State → ℝ}
    (hΓ : ∀ s, 0 ≤ Γ s) (Q : Matrix State κ ℝ) (hQ : Q * Qᵀ = A⁻¹ * diagonal Γ * (A⁻¹)ᵀ) :
    gaussCov A Γ = (stdGaussianPi κ).map (Q *ᵥ ·) := by
  rw [gaussCov_eq_map_mulVec]
  exact map_mulVec_stdGaussianPi_eq _ _ ((gaussCovFactor_mul_transpose A hΓ).trans hQ.symm)

/-- Bridge: the repo's TD Gaussian factor `tdGaussFactor` (`TDInference/SmoothApproximation.lean`) is
`gaussCovFactor (tdA M π μ) (trueGamma M π μ)`. -/
theorem tdGaussFactor_eq_gaussCovFactor {Action : Type} [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) :
    tdGaussFactor M π μ = gaussCovFactor (tdA M π μ) (trueGamma M π μ) := rfl

end GaussCov

/-! ## Non-vacuity -/

/-- Non-vacuity of M4.1 with genuinely different shapes: the law of `Z₁ + Z₂` equals the law of
`√2 · Z`. -/
example :
    (stdGaussianPi (Fin 2)).map ((!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ) *ᵥ ·) =
      (stdGaussianPi (Fin 1)).map ((!![Real.sqrt 2] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ·) := by
  apply map_mulVec_stdGaussianPi_eq
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- Non-vacuity: the image laws are probability measures (not the junk zero measure). -/
example (R : Matrix ι κ ℝ) : ((stdGaussianPi κ).map (R *ᵥ ·)) Set.univ = 1 := measure_univ

end StatisticalRL.Probability
