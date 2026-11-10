import Formalization.Probability.GaussianConvexShell
import Formalization.Analysis.ConvexSmoothIndicator
import Formalization.Probability.ConvexSandwichShell
import Formalization.Probability.GaussianIBP
import Formalization.Probability.GaussianCovCompare
import Formalization.Probability.BerryEsseenStein
import Formalization.Probability.LindebergFinite
import Mathlib.Algebra.Order.Chebyshev

/-!
# Reservoir Lindeberg swap, pass 1: deterministic and one-step ingredients

Infrastructure only; this is a planner/P0 construction (Lindeberg replacement with a Gaussian
reservoir, in the spirit of Bentkus-type smoothing), not a result taken from a cited paper and not a
source result of the formalized monograph. It feeds the all-convex route to Theorem 7.11 but proves
no statement of the book.

Contents:
* `ReservoirCond` (the interface produced by the TD reservoir construction and consumed by the
  reservoir Lindeberg theorem);
* the rectangular twin factor `twinMat`, the swap sets `gaussSet`/`resSet`, the hybrids `hybrid`, the
  hybrid expectations `hexp`, the twin law `twinLaw`, the finite law `lawPexp` and the convex
  distance `cvxDist`;
* matrix and moment bounds for one summand (`matrixAbsSum_le_of_cov`, `sum_cube_add_integral_cube_le`);
* the one-step Lindeberg bounds `abs_step_le_of_reservoir` (Gaussian smoothing by the reservoir) and
  `abs_step_le_of_sandwich` (no smoothing);
* the smoothing inequality `abs_pexp_indicator_sub_le_of_smooth` for an arbitrary set;
* the quadratic-form consequences of `ReservoirCond` and the Gaussian shell bound of the twin law
  `twinLaw_convexShell_le`.
-/

open MeasureTheory ProbabilityTheory Real Matrix Metric
open StatisticalRL.Analysis

namespace StatisticalRL.Probability

/-! ## The reservoir condition -/

/-- Reservoir condition: the Gaussian twins of the last `r` swapped indices have covariance
`≥ (c r / n) I` (Euclidean quadratic form) for every `r₀ ≤ r ≤ n`. -/
def ReservoirCond {κ ι : Type*} [Fintype ι] {n : ℕ} (e : Fin n ≃ κ) (L : κ → Matrix ι ι ℝ)
    (c : ℝ) (r₀ : ℕ) : Prop :=
  ∀ r : ℕ, r₀ ≤ r → r ≤ n → ∀ u : ι → ℝ,
    c * r / n * (u ⬝ᵥ u) ≤
      ∑ m ∈ Finset.univ.filter (fun m : Fin n ↦ n - r ≤ (m : ℕ)),
        u ⬝ᵥ ((L (e m) * (L (e m))ᵀ) *ᵥ u)

section Norms

variable {ι : Type*} [Fintype ι]

/-- The sup norm is dominated by the Euclidean norm: `‖u‖² ≤ u ⬝ᵥ u`. -/
theorem sq_norm_le_dotProduct_self (u : ι → ℝ) : ‖u‖ ^ 2 ≤ u ⬝ᵥ u := by
  have hS : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hle : ‖u‖ ≤ √(u ⬝ᵥ u) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i ↦ ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    simp only [dotProduct, sq]
    exact Finset.single_le_sum (f := fun j ↦ u j * u j) (fun j _ ↦ mul_self_nonneg _)
      (Finset.mem_univ i)
  calc ‖u‖ ^ 2 ≤ √(u ⬝ᵥ u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = u ⬝ᵥ u := Real.sq_sqrt hS

/-- A Euclidean quadratic lower bound implies the sup-norm form used by `GaussianIBP`. -/
theorem quadForm_sup_of_euclid {ι' : Type*} {L : Matrix ι ι' ℝ} [Fintype ι'] {v : ℝ} (hv0 : 0 ≤ v)
    (hv : ∀ u : ι → ℝ, v * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u)) (u : ι → ℝ) :
    v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u) :=
  (mul_le_mul_of_nonneg_left (sq_norm_le_dotProduct_self u) hv0).trans (hv u)

/-- Quadratic form of a finite sum of matrices. -/
theorem dotProduct_sum_mulVec {β : Type*} (s : Finset β) (A : β → Matrix ι ι ℝ) (u : ι → ℝ) :
    u ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ u) = ∑ j ∈ s, u ⬝ᵥ (A j *ᵥ u) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]

/-- A row-sum bound gives a bound on `matrixMaxRowAbsSum`. -/
theorem matrixMaxRowAbsSum_le_of_forall {A : Matrix ι ι ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ∑ j, |A i j| ≤ C) : matrixMaxRowAbsSum A ≤ C := by
  unfold matrixMaxRowAbsSum
  have hs : (Finset.univ.sup fun i ↦ ∑ j, ‖A i j‖₊) ≤ C.toNNReal := Finset.sup_le fun i _ ↦ by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hC, NNReal.coe_sum]
    simpa [Real.norm_eq_abs] using h i
  calc _ ≤ ((C.toNNReal : NNReal) : ℝ) := NNReal.coe_le_coe.2 hs
    _ = C := Real.coe_toNNReal _ hC

end Norms

/-! ## One summand: matrix and moment bounds -/

section Moments

variable {ι : Type*} [Fintype ι] {X : Type*} [Fintype X]

/-- The constant `A₃ = 1 + (S √S)³ · S · 12 e^{1/2}` of the per-step third-moment budget. -/
noncomputable def lindebergMomentConst (ι : Type*) [Fintype ι] : ℝ :=
  1 + ((Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ)) ^ 3 *
    ((Fintype.card ι : ℝ) * (12 * exp (1 / 2)))

theorem lindebergMomentConst_nonneg : 0 ≤ lindebergMomentConst ι := by
  unfold lindebergMomentConst; positivity

/-- A covariance factor of a summand bounded by `b` has `matrixAbsSum ≤ S √S b`. -/
theorem matrixAbsSum_le_of_cov {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY2 : ∀ a b, ∑ x, p x * (Y x a * Y x b) = (L * Lᵀ) a b) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ x, ‖Y x‖ ≤ b) :
    matrixAbsSum L ≤ (Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ) * b := by
  have hrow : ∀ a, ∑ c, |L a c| ≤ √(Fintype.card ι : ℝ) * b := by
    intro a
    have hsq : ∑ c, L a c ^ 2 ≤ b ^ 2 := by
      have e : (L * Lᵀ) a a = ∑ c, L a c ^ 2 := by
        simp [Matrix.mul_apply, sq]
      rw [← e, ← hY2 a a]
      calc ∑ x, p x * (Y x a * Y x a) ≤ ∑ x, p x * b ^ 2 := Finset.sum_le_sum fun x _ ↦ by
            refine mul_le_mul_of_nonneg_left ?_ (hp0 x)
            have h := (abs_apply_le_norm (Y x) a).trans (hb x)
            rw [← sq, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = b ^ 2 := by rw [← Finset.sum_mul, hp1, one_mul]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c ↦ |L a c|)
    simp only [sq_abs, Finset.card_univ] at hcs
    have hrhs : √(Fintype.card ι : ℝ) * b = √((Fintype.card ι : ℝ) * b ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb0]
    rw [hrhs]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (hcs.trans
      (mul_le_mul_of_nonneg_left hsq (by positivity))))
  calc matrixAbsSum L = ∑ a, ∑ c, |L a c| := rfl
    _ ≤ ∑ _a : ι, √(Fintype.card ι : ℝ) * b := Finset.sum_le_sum fun a _ ↦ hrow a
    _ = _ := by simp [mul_assoc]

/-- `∫ ‖L z‖³ dν ≤ matrixAbsSum L ³ · S · 12 e^{1/2}`. -/
theorem integral_norm_mulVec_pow_three_le (L : Matrix ι ι ℝ) :
    ∫ z, ‖L *ᵥ z‖ ^ 3 ∂stdGaussianPi ι ≤
      matrixAbsSum L ^ 3 * ((Fintype.card ι : ℝ) * (12 * exp (1 / 2))) := by
  calc ∫ z, ‖L *ᵥ z‖ ^ 3 ∂stdGaussianPi ι ≤ ∫ z, matrixAbsSum L ^ 3 * ‖z‖ ^ 3 ∂stdGaussianPi ι :=
        integral_mono (integrable_norm_mulVec_pow_three_stdGaussianPi L)
          (integrable_norm_pow_three_stdGaussianPi.const_mul _) fun z ↦ by
            have h := norm_mulVec_le_matrixAbsSum L z
            calc ‖L *ᵥ z‖ ^ 3 ≤ (matrixAbsSum L * ‖z‖) ^ 3 :=
                  pow_le_pow_left₀ (norm_nonneg _) h 3
              _ = matrixAbsSum L ^ 3 * ‖z‖ ^ 3 := by ring
    _ = matrixAbsSum L ^ 3 * ∫ z, ‖z‖ ^ 3 ∂stdGaussianPi ι := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left integral_norm_pow_three_stdGaussianPi_le
          (pow_nonneg (matrixAbsSum_nonneg L) 3)

/-- Per-step third-moment budget: `E‖Y‖³ + E‖L z‖³ ≤ A₃ b³`. -/
theorem sum_cube_add_integral_cube_le {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY2 : ∀ a b, ∑ x, p x * (Y x a * Y x b) = (L * Lᵀ) a b) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ x, ‖Y x‖ ≤ b) :
    ∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂stdGaussianPi ι ≤
      lindebergMomentConst ι * b ^ 3 := by
  have hd : ∑ x, p x * ‖Y x‖ ^ 3 ≤ b ^ 3 :=
    (Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hb x) 3) (hp0 x)).trans
      (by rw [← Finset.sum_mul, hp1, one_mul])
  have hm := matrixAbsSum_le_of_cov hp0 hp1 hY2 hb0 hb
  have hg := integral_norm_mulVec_pow_three_le L
  have hm3 : matrixAbsSum L ^ 3 ≤
      ((Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ) * b) ^ 3 :=
    pow_le_pow_left₀ (matrixAbsSum_nonneg L) hm 3
  have hC : 0 ≤ (Fintype.card ι : ℝ) * (12 * exp (1 / 2)) := by positivity
  calc _ ≤ b ^ 3 + ((Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ) * b) ^ 3 *
          ((Fintype.card ι : ℝ) * (12 * exp (1 / 2))) :=
        add_le_add hd (hg.trans (mul_le_mul_of_nonneg_right hm3 hC))
    _ = lindebergMomentConst ι * b ^ 3 := by unfold lindebergMomentConst; ring

end Moments

/-! ## Taylor adapters and the one-step swap -/

section Swap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bound on the third derivative makes the second derivative Lipschitz. -/
theorem norm_fderiv_fderiv_sub_le_of_iteratedFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} (hF : ContDiff ℝ 3 F)
    {M : ℝ} (h : ∀ x, ‖iteratedFDeriv ℝ 3 F x‖ ≤ M) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ M * ‖x - y‖ := by
  have hd : Differentiable ℝ fun z ↦ iteratedFDeriv ℝ 2 F z :=
    hF.differentiable_iteratedFDeriv (by norm_num)
  have hb : ∀ z, ‖fderiv ℝ (fun z ↦ iteratedFDeriv ℝ 2 F z) z‖ ≤ M := fun z ↦ by
    rw [norm_fderiv_iteratedFDeriv]; exact h z
  have hlip := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hd z)
    (fun z _ ↦ hb z) (Set.mem_univ y) (Set.mem_univ x)
  have key : ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ =
      ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ := by
    rw [← dist_eq_norm (iteratedFDeriv ℝ 2 F x), ← dist_eq_norm (fderiv ℝ (fderiv ℝ F) x)]
    simp only [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_zero_eq_comp,
      Function.comp_apply, LinearIsometryEquiv.dist_map]
  rw [key]; exact hlip

omit [DecidableEq ι] in
/-- `‖D F x‖ = ‖D¹ F x‖` as an iterated derivative. -/
theorem norm_fderiv_eq_norm_iteratedFDeriv_one (F : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    ‖fderiv ℝ F x‖ = ‖iteratedFDeriv ℝ 1 F x‖ := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ F), norm_iteratedFDeriv_fderiv]

/-- **One Lindeberg swap** for a `C³` test with bounded first and third derivatives:
`|∑ p F(U + Y) − ∫ F(U + L z) dν| ≤ M/6 · A₃ b³`. -/
theorem abs_sum_sub_integral_le_of_iteratedFDeriv {X : Type*} [Fintype X] {p : X → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ a, ∑ x, p x * Y x a = 0)
    (hY2 : ∀ a b, ∑ x, p x * (Y x a * Y x b) = (L * Lᵀ) a b)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ x, ‖Y x‖ ≤ b)
    {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) {L₁ M : ℝ}
    (h1 : ∀ x, ‖iteratedFDeriv ℝ 1 F x‖ ≤ L₁) (h3 : ∀ x, ‖iteratedFDeriv ℝ 3 F x‖ ≤ M)
    (U : ι → ℝ) :
    |∑ x, p x * F (U + Y x) - ∫ z, F (U + L *ᵥ z) ∂stdGaussianPi ι| ≤
      M / 6 * (lindebergMomentConst ι * b ^ 3) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h3 0)
  have hL₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ L₁ := fun x ↦ by
    rw [norm_fderiv_eq_norm_iteratedFDeriv_one]; exact h1 x
  refine (abs_sum_sub_integral_le_of_moments hp0 hp1 hY1 hY2 (hF.of_le (by norm_num)) hL₁
    (norm_fderiv_fderiv_sub_le_of_iteratedFDeriv hF h3) U).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_cube_add_integral_cube_le hp0 hp1 hY2 hb0 hb)
    (by positivity)

omit [DecidableEq ι] in
/-- A continuous `[0,1]`-valued function is integrable for a probability measure. -/
theorem integrable_of_continuous_mem_Icc {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {g : E → ℝ}
    (hg : Continuous g) (h01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) : Integrable g μ :=
  (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable (ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)

omit [Fintype ι] [DecidableEq ι] in
theorem norm_le_one_of_mem_Icc {φ : (ι → ℝ) → ℝ} (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (y : ι → ℝ) : ‖φ y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(h01 y).1], (h01 y).2⟩

omit [DecidableEq ι] in
/-- Smoothing by a reservoir with Euclidean covariance `≥ v I`: `gaussSmooth φ R` is `C³` with
`‖D³‖ ≤ gaussDerivConst 3 · S³ · (v √v)⁻¹` and bounded `D¹` (constants free of `ι'`). -/
theorem gaussSmooth_reservoir_bounds {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) (hbd : ∀ k : ℕ, ∃ C, ∀ y, ‖iteratedFDeriv ℝ k φ y‖ ≤ C)
    {ι' : Type*} [Fintype ι'] (R : Matrix ι ι' ℝ) {v : ℝ} (hv0 : 0 < v)
    (hv : ∀ u : ι → ℝ, v * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((R * Rᵀ) *ᵥ u)) :
    ContDiff ℝ 3 (gaussSmooth φ R) ∧
    (∀ x, ‖iteratedFDeriv ℝ 3 (gaussSmooth φ R) x‖ ≤
      gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 * (v * √v)⁻¹) ∧
    (∀ x, ‖iteratedFDeriv ℝ 1 (gaussSmooth φ R) x‖ ≤
      gaussDerivConst 1 * (Fintype.card ι : ℝ) ^ 1 * (√v)⁻¹) := by
  have hφ3 : ContDiff ℝ (3 : ℕ) φ := contDiff_infty.1 hφ 3
  have hbd3 : ∀ j ≤ 3, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C := fun j _ ↦ hbd j
  have hB : ∀ y, ‖φ y‖ ≤ 1 := norm_le_one_of_mem_Icc h01
  have hsup := quadForm_sup_of_euclid hv0.le hv
  refine ⟨contDiff_gaussSmooth hφ3 hbd3 R, fun x ↦ ?_, fun x ↦ ?_⟩
  · refine (norm_iteratedFDeriv_gaussSmooth_le hφ3 hbd3 hB hv0 hsup (k := 3) le_rfl x).trans_eq ?_
    have : v ^ (-((3 : ℕ) : ℝ) / 2) = (v * √v)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hv0.le (by norm_num), ← Real.rpow_neg hv0.le]
      norm_num
    rw [this]; ring
  · refine (norm_iteratedFDeriv_gaussSmooth_le hφ3 hbd3 hB hv0 hsup (k := 1) (by norm_num)
      x).trans_eq ?_
    have : v ^ (-((1 : ℕ) : ℝ) / 2) = (√v)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hv0.le]; norm_num
    rw [this]; ring

/-- **Step (a), pointwise: reservoir smoothing.** With `R` the factor of a reservoir of Euclidean
covariance `≥ v I`, the swap of `Y` against its twin `L z` in the presence of the reservoir costs
`gaussDerivConst 3 · S³ (v √v)⁻¹ / 6 · A₃ b³`, uniformly in the base point `U`. -/
theorem abs_step_le_of_reservoir {X : Type*} [Fintype X] {p : X → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ a, ∑ x, p x * Y x a = 0)
    (hY2 : ∀ a b, ∑ x, p x * (Y x a * Y x b) = (L * Lᵀ) a b)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ x, ‖Y x‖ ≤ b)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hbd : ∀ k : ℕ, ∃ C, ∀ y, ‖iteratedFDeriv ℝ k φ y‖ ≤ C)
    {ι' : Type*} [Fintype ι'] (R : Matrix ι ι' ℝ) {v : ℝ} (hv0 : 0 < v)
    (hv : ∀ u : ι → ℝ, v * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((R * Rᵀ) *ᵥ u)) (U : ι → ℝ) :
    |∑ x, p x * ∫ w, φ (U + Y x + R *ᵥ w) ∂stdGaussianPi ι' -
        ∫ z, ∫ w, φ (U + L *ᵥ z + R *ᵥ w) ∂stdGaussianPi ι' ∂stdGaussianPi ι| ≤
      gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 * (v * √v)⁻¹ / 6 *
        (lindebergMomentConst ι * b ^ 3) := by
  obtain ⟨hc, h3, h1⟩ := gaussSmooth_reservoir_bounds hφ h01 hbd R hv0 hv
  exact abs_sum_sub_integral_le_of_iteratedFDeriv hp0 hp1 hY1 hY2 hb0 hb hc h1 h3 U

/-- **Step (c), pointwise: no smoothing.** For a sandwich-type test `φ` at scale `ε`, the swap
costs `sandwichConst ι 3 / ε³ / 6 · A₃ b³`, uniformly in the base point and the reservoir. -/
theorem abs_step_le_of_sandwich {X : Type*} [Fintype X] {p : X → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ a, ∑ x, p x * Y x a = 0)
    (hY2 : ∀ a b, ∑ x, p x * (Y x a * Y x b) = (L * Lᵀ) a b)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ x, ‖Y x‖ ≤ b)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hd : ∀ (k : ℕ) (x : ι → ℝ),
      ‖iteratedFDeriv ℝ k φ x‖ ≤ ConvexSmoothIndicator.sandwichConst ι k / ε ^ k)
    {ι' : Type*} [Fintype ι'] (R : Matrix ι ι' ℝ) (U : ι → ℝ) :
    |∑ x, p x * ∫ w, φ (U + Y x + R *ᵥ w) ∂stdGaussianPi ι' -
        ∫ z, ∫ w, φ (U + L *ᵥ z + R *ᵥ w) ∂stdGaussianPi ι' ∂stdGaussianPi ι| ≤
      ConvexSmoothIndicator.sandwichConst ι 3 / ε ^ 3 / 6 * (lindebergMomentConst ι * b ^ 3) := by
  set γ := stdGaussianPi ι'
  set ν := stdGaussianPi ι
  have hφc : Continuous φ := hφ.continuous
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hRc : Continuous fun w : ι' → ℝ ↦ R *ᵥ w := continuous_mulVec_const R
  have hLc : Continuous fun z : ι → ℝ ↦ L *ᵥ z := continuous_mulVec_const L
  -- data side, moved inside the integral
  have hY : ∑ x, p x * ∫ w, φ (U + Y x + R *ᵥ w) ∂γ =
      ∫ w, ∑ x, p x * φ (U + R *ᵥ w + Y x) ∂γ := by
    have hI : ∀ x ∈ (Finset.univ : Finset X),
        Integrable (fun w ↦ p x * φ (U + R *ᵥ w + Y x)) γ := fun x _ ↦
      (integrable_of_continuous_mem_Icc (g := fun w ↦ φ (U + R *ᵥ w + Y x))
        (hφc.comp ((continuous_const.add hRc).add continuous_const)) (fun w ↦ h01 _)).const_mul _
    rw [integral_finset_sum _ hI]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← integral_const_mul]
    congr 1; funext w; rw [add_right_comm]
  -- Gaussian side, integrals swapped
  have hint2 : Integrable (Function.uncurry fun (z : ι → ℝ) (w : ι' → ℝ) ↦
      φ (U + L *ᵥ z + R *ᵥ w)) (ν.prod γ) :=
    integrable_of_continuous_mem_Icc
      (hφc.comp ((continuous_const.add (hLc.comp continuous_fst)).add (hRc.comp continuous_snd)))
      (fun q ↦ h01 _)
  have hG : ∫ z, ∫ w, φ (U + L *ᵥ z + R *ᵥ w) ∂γ ∂ν =
      ∫ w, ∫ z, φ (U + R *ᵥ w + L *ᵥ z) ∂ν ∂γ := by
    rw [integral_integral_swap hint2]
    congr 1; funext w; congr 1; funext z; rw [add_right_comm]
  have hgs : Continuous fun w : ι' → ℝ ↦ ∫ z, φ (U + R *ᵥ w + L *ᵥ z) ∂ν :=
    (continuous_gaussSmooth hφc (norm_le_one_of_mem_Icc h01) L).comp
      (continuous_const.add hRc)
  have hgsI : Integrable (fun w : ι' → ℝ ↦ ∫ z, φ (U + R *ᵥ w + L *ᵥ z) ∂ν) γ := by
    refine (integrable_const (1 : ℝ)).mono' hgs.aestronglyMeasurable (ae_of_all _ fun w ↦ ?_)
    exact norm_gaussSmooth_le (norm_le_one_of_mem_Icc h01) L (U + R *ᵥ w)
  have hYI : Integrable (fun w : ι' → ℝ ↦ ∑ x, p x * φ (U + R *ᵥ w + Y x)) γ :=
    integrable_finset_sum _ fun x _ ↦ (integrable_of_continuous_mem_Icc
      (hφc.comp ((continuous_const.add hRc).add continuous_const)) (fun w ↦ h01 _)).const_mul _
  rw [hY, hG, ← integral_sub hYI hgsI]
  have hbound : ∀ w : ι' → ℝ, ‖∑ x, p x * φ (U + R *ᵥ w + Y x) -
      ∫ z, φ (U + R *ᵥ w + L *ᵥ z) ∂ν‖ ≤
      ConvexSmoothIndicator.sandwichConst ι 3 / ε ^ 3 / 6 * (lindebergMomentConst ι * b ^ 3) := by
    intro w
    rw [Real.norm_eq_abs]
    exact abs_sum_sub_integral_le_of_iteratedFDeriv hp0 hp1 hY1 hY2 hb0 hb hφ3 (hd 1) (hd 3) _
  have := norm_integral_le_of_norm_le_const (μ := γ) (ae_of_all _ hbound)
  simpa [Real.norm_eq_abs] using this

end Swap

/-! ## The smoothing inequality -/

section Smoothing

variable {ι : Type*} [Fintype ι]

/-- The open thickening lies in `K` union the shell. -/
theorem thickening_subset_union_shell (K : Set (ι → ℝ)) {ε : ℝ} (hε : 0 ≤ ε) :
    thickening ε K ⊆ K ∪ (cthickening ε K ∩ cthickening ε (interior K)ᶜ) := by
  intro x hx
  by_cases h : x ∈ K
  · exact Or.inl h
  · exact Or.inr (ConvexSandwichShell.thickening_diff_subset_convexShell K hε ⟨hx, h⟩)

/-- Points of the open set `(cthickening ε (interior K)ᶜ)ᶜ` have their closed `ε`-ball in `K`. -/
theorem closedBall_subset_of_mem_inner {K : Set (ι → ℝ)} {ε : ℝ} {x : ι → ℝ}
    (hx : x ∈ (cthickening ε (interior K)ᶜ)ᶜ) : closedBall x ε ⊆ K := by
  intro y hy
  by_contra hyK
  exact hx (mem_cthickening_of_dist_le x y ε _ (fun h ↦ hyK (interior_subset h))
    (by rw [dist_comm]; exact mem_closedBall.1 hy))

/-- `K` lies in the open inner set union the shell. -/
theorem subset_inner_union_shell (K : Set (ι → ℝ)) (ε : ℝ) :
    K ⊆ (cthickening ε (interior K)ᶜ)ᶜ ∪ (cthickening ε K ∩ cthickening ε (interior K)ᶜ) := by
  intro x hx
  by_cases h : x ∈ cthickening ε (interior K)ᶜ
  · exact Or.inr ⟨self_subset_cthickening _ hx, h⟩
  · exact Or.inl h

/-- **Smoothing inequality** (any set `K`; convexity enters only through the shell bound `hsh`).
If every sandwich-type test at scale `ε` has expectation within `Δ` of its `ν'`-integral, and the
`ε`-shell of `K` has `ν'`-mass at most `σ`, then `|P(Z ∈ K) − ν'(K)| ≤ Δ + σ`. -/
theorem abs_pexp_indicator_sub_le_of_smooth {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : κ → Type*} [∀ i, Fintype (X i)] {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (Z : (∀ i, X i) → ι → ℝ) (ν' : Measure (ι → ℝ)) [IsProbabilityMeasure ν'] {ε σ Δ : ℝ}
    (hε : 0 < ε) (K : Set (ι → ℝ))
    (hsh : ν'.real (cthickening ε K ∩ cthickening ε (interior K)ᶜ) ≤ σ)
    (hsm : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ (k : ℕ) (x : ι → ℝ),
        ‖iteratedFDeriv ℝ k φ x‖ ≤ ConvexSmoothIndicator.sandwichConst ι k / ε ^ k) →
      |Stein.pexp p (fun ω ↦ φ (Z ω)) - ∫ y, φ y ∂ν'| ≤ Δ) :
    |Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) - ν'.real K| ≤ Δ + σ := by
  -- upper bound
  obtain ⟨φu, hu_s, hu01, hu1, hu0, hud⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_upper K hε
  have hup1 : Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) ≤
      Stein.pexp p (fun ω ↦ φu (Z ω)) :=
    Stein.pexp_mono hp0 fun ω ↦ by
      by_cases h : Z ω ∈ K
      · rw [Set.indicator_of_mem h, hu1 _ h]
      · rw [Set.indicator_of_notMem h]; exact (hu01 _).1
  have hup2 := (abs_le.1 (hsm φu hu_s hu01 hud)).2
  have hthick : IsOpen (thickening ε K) := isOpen_thickening
  have hup3 : ∫ y, φu y ∂ν' ≤ ν'.real (thickening ε K) := by
    rw [← integral_indicator_one hthick.measurableSet]
    refine integral_mono (integrable_of_continuous_mem_Icc hu_s.continuous hu01)
      ((integrable_const (1 : ℝ)).indicator hthick.measurableSet) fun x ↦ ?_
    by_cases h : x ∈ thickening ε K
    · rw [Set.indicator_of_mem h]; exact (hu01 x).2
    · rw [Set.indicator_of_notMem h, hu0 x h]
  have hup4 : ν'.real (thickening ε K) ≤
      ν'.real K + ν'.real (cthickening ε K ∩ cthickening ε (interior K)ᶜ) :=
    (measureReal_mono (thickening_subset_union_shell K hε.le)).trans (measureReal_union_le _ _)
  -- lower bound
  obtain ⟨φl, hl_s, hl01, hl1, hl0, hld⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_lower K hε
  have hMo : IsOpen (cthickening ε (interior K)ᶜ)ᶜ := isClosed_cthickening.isOpen_compl
  have hlo1 : Stein.pexp p (fun ω ↦ φl (Z ω)) ≤
      Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) :=
    Stein.pexp_mono hp0 fun ω ↦ by
      by_cases h : Z ω ∈ K
      · rw [Set.indicator_of_mem h]; exact (hl01 _).2
      · rw [Set.indicator_of_notMem h, hl0 _ h]
  have hlo2 := (abs_le.1 (hsm φl hl_s hl01 hld)).1
  have hlo3 : ν'.real (cthickening ε (interior K)ᶜ)ᶜ ≤ ∫ y, φl y ∂ν' := by
    rw [← integral_indicator_one hMo.measurableSet]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hMo.measurableSet)
      (integrable_of_continuous_mem_Icc hl_s.continuous hl01) fun x ↦ ?_
    by_cases h : x ∈ (cthickening ε (interior K)ᶜ)ᶜ
    · rw [Set.indicator_of_mem h, hl1 x (closedBall_subset_of_mem_inner h)]; rfl
    · rw [Set.indicator_of_notMem h]; exact (hl01 x).1
  have hlo4 : ν'.real K ≤ ν'.real (cthickening ε (interior K)ᶜ)ᶜ +
      ν'.real (cthickening ε K ∩ cthickening ε (interior K)ᶜ) :=
    (measureReal_mono (subset_inner_union_shell K ε)).trans (measureReal_union_le _ _)
  rw [abs_le]; constructor <;> linarith

end Smoothing

/-! ## Twin matrices, swap sets, hybrids -/

section Hybrid

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] {n : ℕ}

/-- Rectangular factor of the Gaussian twins of the indices in `s`: block `j ∈ s` of the column
index `κ × ι` carries `L j`, the other blocks are zero. -/
def twinMat (L : κ → Matrix ι ι ℝ) (s : Finset κ) : Matrix ι (κ × ι) ℝ :=
  Matrix.of fun a c ↦ if c.1 ∈ s then L c.1 a c.2 else 0

omit [Fintype κ] [Fintype ι] in
theorem twinMat_apply (L : κ → Matrix ι ι ℝ) (s : Finset κ) (a : ι) (c : κ × ι) :
    twinMat L s a c = if c.1 ∈ s then L c.1 a c.2 else 0 := rfl

/-- `twinMat L s w = ∑_{j ∈ s} L j w_j`, with `w_j = fun a ↦ w (j, a)` the `j`-th block. -/
theorem twinMat_mulVec (L : κ → Matrix ι ι ℝ) (s : Finset κ) (w : κ × ι → ℝ) :
    twinMat L s *ᵥ w = ∑ j ∈ s, L j *ᵥ (fun a ↦ w (j, a)) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, twinMat_apply, Fintype.sum_prod_type, Finset.sum_apply]
  have : ∀ j, (∑ x, (if j ∈ s then L j a x else 0) * w (j, x)) =
      if j ∈ s then ∑ x, L j a x * w (j, x) else 0 := by
    intro j; by_cases hj : j ∈ s <;> simp [hj]
  simp only [this]
  rw [Fintype.sum_ite_mem]

/-- Covariance of the twin factor: `twinMat L s (twinMat L s)ᵀ = ∑_{j ∈ s} L j (L j)ᵀ`. -/
theorem twinMat_mul_transpose (L : κ → Matrix ι ι ℝ) (s : Finset κ) :
    twinMat L s * (twinMat L s)ᵀ = ∑ j ∈ s, L j * (L j)ᵀ := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, twinMat_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  have : ∀ j, (∑ x, (if j ∈ s then L j a x else 0) * (if j ∈ s then L j b x else 0)) =
      if j ∈ s then ∑ x, L j a x * L j b x else 0 := by
    intro j; by_cases hj : j ∈ s <;> simp [hj]
  simp only [this]
  rw [Fintype.sum_ite_mem]

/-- The twin factor ignores blocks outside `s`. -/
theorem twinMat_mulVec_congr (L : κ → Matrix ι ι ℝ) (s : Finset κ) {w w' : κ × ι → ℝ}
    (h : ∀ j ∈ s, ∀ a, w (j, a) = w' (j, a)) : twinMat L s *ᵥ w = twinMat L s *ᵥ w' := by
  rw [twinMat_mulVec, twinMat_mulVec]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  congr 1; funext a; exact h j hj a

omit [Fintype κ] [Fintype ι] in
theorem twinMat_empty (L : κ → Matrix ι ι ℝ) : twinMat L ∅ = 0 := by
  ext a c; simp [twinMat_apply]

/-- Twin factor of `insert i s` with `i ∉ s`. -/
theorem twinMat_insert_mulVec (L : κ → Matrix ι ι ℝ) {s : Finset κ} {i : κ} (hi : i ∉ s)
    (w : κ × ι → ℝ) :
    twinMat L (insert i s) *ᵥ w = L i *ᵥ (fun a ↦ w (i, a)) + twinMat L s *ᵥ w := by
  rw [twinMat_mulVec, twinMat_mulVec, Finset.sum_insert hi]

/-- Indices still Gaussian at step `k`. -/
def gaussSet (e : Fin n ≃ κ) (k : ℕ) : Finset κ :=
  (Finset.univ.filter fun m : Fin n ↦ k ≤ (m : ℕ)).map e.toEmbedding

/-- The reservoir at step `k`: indices swapped strictly after step `k`. -/
def resSet (e : Fin n ≃ κ) (k : ℕ) : Finset κ :=
  (Finset.univ.filter fun m : Fin n ↦ k < (m : ℕ)).map e.toEmbedding

/-- Non-Gaussian prefix: the summands swapped before step `k`. -/
def prefixSum (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (k : ℕ) (ω : ∀ i, X i) : ι → ℝ :=
  ∑ m : Fin n, if (m : ℕ) < k then Y (e m) (ω (e m)) else 0

/-- Hybrid at step `k`: `H_k = ∑_{m<k} Y_{e m} + ∑_{m ≥ k} L_{e m} w_{e m}`. -/
def hybrid (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ) (k : ℕ)
    (ω : ∀ i, X i) (w : κ × ι → ℝ) : ι → ℝ :=
  prefixSum e Y k ω + twinMat L (gaussSet e k) *ᵥ w

/-- Twin law `N(0, ∑ᵢ Lᵢ Lᵢᵀ)`, the Lindeberg endpoint. -/
noncomputable def twinLaw (L : κ → Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (stdGaussianPi (κ × ι)).map (twinMat L Finset.univ *ᵥ ·)

/-- Expected test value at hybrid step `k`. -/
noncomputable def hexp (p : ∀ i, X i → ℝ) (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ)
    (L : κ → Matrix ι ι ℝ) (f : (ι → ℝ) → ℝ) (k : ℕ) : ℝ :=
  Stein.pexp p (fun ω ↦ ∫ w, f (hybrid e Y L k ω w) ∂stdGaussianPi (κ × ι))

/-- Law of `Z` under the product of the finite laws `p i`. -/
noncomputable def lawPexp (p : ∀ i, X i → ℝ) (Z : (∀ i, X i) → ι → ℝ) : Measure (ι → ℝ) :=
  ∑ ω, ENNReal.ofReal (∏ i, p i (ω i)) • Measure.dirac (Z ω)

/-- Convex distance between two measures on `ι → ℝ`: supremum over Borel convex sets. -/
noncomputable def cvxDist (μ ν : Measure (ι → ℝ)) : ℝ :=
  ⨆ K : {K : Set (ι → ℝ) // Convex ℝ K ∧ MeasurableSet K}, |μ.real K.1 - ν.real K.1|

omit [Fintype κ] [DecidableEq κ] in
theorem gaussSet_succ (e : Fin n ≃ κ) (k : ℕ) : gaussSet e (k + 1) = resSet e k := rfl

omit [Fintype κ] [DecidableEq κ] in
theorem not_mem_resSet (e : Fin n ≃ κ) {k : ℕ} (hk : k < n) : e ⟨k, hk⟩ ∉ resSet e k := by
  simp only [resSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.coe_toEmbedding, not_exists, not_and]
  intro m hm heq
  have := congrArg Fin.val (e.injective heq)
  simp at this; omega

omit [Fintype κ] in
theorem gaussSet_eq_insert (e : Fin n ≃ κ) {k : ℕ} (hk : k < n) :
    gaussSet e k = insert (e ⟨k, hk⟩) (resSet e k) := by
  ext j
  simp only [gaussSet, resSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rcases Nat.lt_or_eq_of_le hm with h | h
    · exact Or.inr ⟨m, h, rfl⟩
    · left; congr 1; ext; exact h.symm
  · rintro (rfl | ⟨m, hm, rfl⟩)
    · exact ⟨⟨k, hk⟩, le_rfl, rfl⟩
    · exact ⟨m, hm.le, rfl⟩

omit [DecidableEq κ] in
theorem gaussSet_zero (e : Fin n ≃ κ) : gaussSet e 0 = Finset.univ := by
  simp only [gaussSet, zero_le, Finset.filter_true]
  exact Finset.map_univ_equiv e

omit [Fintype κ] [DecidableEq κ] in
theorem gaussSet_n (e : Fin n ≃ κ) : gaussSet e n = ∅ := by
  simp only [gaussSet, Finset.map_eq_empty, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_implies, not_le]
  exact fun m ↦ m.2

omit [Fintype κ] [DecidableEq κ] [(i : κ) → Fintype (X i)] [Fintype ι] in
theorem prefixSum_zero (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (ω : ∀ i, X i) :
    prefixSum e Y 0 ω = 0 := by
  simp [prefixSum]

omit [DecidableEq κ] [(i : κ) → Fintype (X i)] [Fintype ι] in
theorem prefixSum_n (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (ω : ∀ i, X i) :
    prefixSum e Y n ω = ∑ i, Y i (ω i) := by
  simp only [prefixSum, Fin.is_lt, if_true]
  exact Equiv.sum_comp e (fun i ↦ Y i (ω i))

omit [Fintype κ] [DecidableEq κ] [(i : κ) → Fintype (X i)] [Fintype ι] in
theorem prefixSum_succ (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) {k : ℕ} (hk : k < n)
    (ω : ∀ i, X i) :
    prefixSum e Y (k + 1) ω = prefixSum e Y k ω + Y (e ⟨k, hk⟩) (ω (e ⟨k, hk⟩)) := by
  unfold prefixSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
  have h1 : (if ((⟨k, hk⟩ : Fin n) : ℕ) < k + 1 then Y (e ⟨k, hk⟩) (ω (e ⟨k, hk⟩)) else 0) =
      Y (e ⟨k, hk⟩) (ω (e ⟨k, hk⟩)) := if_pos (Nat.lt_succ_self k)
  have h2 : (if ((⟨k, hk⟩ : Fin n) : ℕ) < k then Y (e ⟨k, hk⟩) (ω (e ⟨k, hk⟩)) else 0) = 0 :=
    if_neg (lt_irrefl k)
  rw [h1, h2, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hne : (m : ℕ) ≠ k := fun h ↦ (Finset.mem_erase.1 hm).1 (Fin.ext h)
  by_cases h : (m : ℕ) < k
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

omit [Fintype κ] [(i : κ) → Fintype (X i)] [Fintype ι] in
theorem prefixSum_update (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) {k : ℕ} (hk : k < n)
    (ω : ∀ i, X i) (y : X (e ⟨k, hk⟩)) :
    prefixSum e Y k (Function.update ω (e ⟨k, hk⟩) y) = prefixSum e Y k ω := by
  unfold prefixSum
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  by_cases h : (m : ℕ) < k
  · rw [if_pos h, if_pos h]
    have hne : e m ≠ e ⟨k, hk⟩ := fun heq ↦ by
      have := congrArg Fin.val (e.injective heq); simp at this; omega
    rw [Function.update_of_ne hne]
  · rw [if_neg h, if_neg h]

omit [(i : κ) → Fintype (X i)] in
/-- Hybrid after the swap at step `k`: `H_{k+1} = P_k + Y_i + R_k w`. -/
theorem hybrid_succ_eq (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ) {k : ℕ}
    (hk : k < n) (ω : ∀ i, X i) (w : κ × ι → ℝ) :
    hybrid e Y L (k + 1) ω w =
      prefixSum e Y k ω + Y (e ⟨k, hk⟩) (ω (e ⟨k, hk⟩)) + twinMat L (resSet e k) *ᵥ w := by
  rw [hybrid, prefixSum_succ e Y hk, gaussSet_succ]

omit [(i : κ) → Fintype (X i)] in
/-- Hybrid before the swap at step `k`: `H_k = P_k + L_i w_i + R_k w`. -/
theorem hybrid_eq (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ) {k : ℕ}
    (hk : k < n) (ω : ∀ i, X i) (w : κ × ι → ℝ) :
    hybrid e Y L k ω w = prefixSum e Y k ω + L (e ⟨k, hk⟩) *ᵥ (fun a ↦ w (e ⟨k, hk⟩, a)) +
      twinMat L (resSet e k) *ᵥ w := by
  rw [hybrid, gaussSet_eq_insert e hk, twinMat_insert_mulVec L (not_mem_resSet e hk), add_assoc]

/-- The last hybrid is the sum of the summands. -/
theorem hexp_n {p : ∀ i, X i → ℝ} (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ)
    (f : (ι → ℝ) → ℝ) : hexp p e Y L f n = Stein.pexp p (fun ω ↦ f (∑ i, Y i (ω i))) := by
  unfold hexp
  congr 1; funext ω
  simp only [hybrid, gaussSet_n, twinMat_empty, Matrix.zero_mulVec, add_zero, prefixSum_n]
  simp

/-- The first hybrid has the twin law. -/
theorem hexp_zero {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (e : Fin n ≃ κ)
    (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ) {f : (ι → ℝ) → ℝ} (hf : Continuous f) :
    hexp p e Y L f 0 = ∫ y, f y ∂(twinLaw L) := by
  unfold hexp
  simp only [hybrid, gaussSet_zero, prefixSum_zero, zero_add]
  rw [Stein.pexp_const hp1, twinLaw, integral_map
    (continuous_mulVec_const _).measurable.aemeasurable hf.aestronglyMeasurable]

/-- The data-side step: averaging out coordinate `e k` first. -/
theorem hexp_succ_eq {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (e : Fin n ≃ κ)
    (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ) (f : (ι → ℝ) → ℝ) {k : ℕ} (hk : k < n) :
    hexp p e Y L f (k + 1) = Stein.pexp p (fun ω ↦ ∑ y, p (e ⟨k, hk⟩) y *
      ∫ w, f (prefixSum e Y k ω + Y (e ⟨k, hk⟩) y + twinMat L (resSet e k) *ᵥ w)
        ∂stdGaussianPi (κ × ι)) := by
  unfold hexp
  simp only [hybrid_succ_eq e Y L hk]
  exact Stein.pexp_comp_coord hp1 (e ⟨k, hk⟩)
    (fun y ω ↦ ∫ w, f (prefixSum e Y k ω + Y (e ⟨k, hk⟩) y + twinMat L (resSet e k) *ᵥ w)
      ∂stdGaussianPi (κ × ι))
    (fun y ω b ↦ by simp only [prefixSum_update e Y hk])

end Hybrid

/-! ## Consequences of the reservoir condition and the twin-law shell -/

section Reservoir

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι] {n : ℕ}

/-- The reservoir at step `k` (size `n - 1 - k ≥ r₀`) has Euclidean covariance
`≥ (c (n-1-k) / n) I`. -/
theorem reservoir_quadForm {e : Fin n ≃ κ} {L : κ → Matrix ι ι ℝ} {c : ℝ} {r₀ : ℕ}
    (hres : ReservoirCond e L c r₀) {k : ℕ} (hk : k < n) (hr : r₀ ≤ n - 1 - k) (u : ι → ℝ) :
    c * ((n - 1 - k : ℕ) : ℝ) / n * (u ⬝ᵥ u) ≤
      u ⬝ᵥ ((twinMat L (resSet e k) * (twinMat L (resSet e k))ᵀ) *ᵥ u) := by
  refine (hres (n - 1 - k) hr (by omega) u).trans_eq ?_
  rw [twinMat_mul_transpose, dotProduct_sum_mulVec, resSet, Finset.sum_map]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

/-- Total covariance `∑ᵢ Lᵢ Lᵢᵀ ≥ c I` (the reservoir condition at `r = n`). -/
theorem total_quadForm {e : Fin n ≃ κ} {L : κ → Matrix ι ι ℝ} {c : ℝ} {r₀ : ℕ}
    (hres : ReservoirCond e L c r₀) (hr₀ : r₀ ≤ n) (hn : 0 < n) (u : ι → ℝ) :
    c * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((twinMat L Finset.univ * (twinMat L Finset.univ)ᵀ) *ᵥ u) := by
  have h := hres n hr₀ le_rfl u
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [mul_div_assoc, div_self hn', mul_one] at h
  refine h.trans_eq ?_
  rw [twinMat_mul_transpose, dotProduct_sum_mulVec]
  rw [show (Finset.univ.filter fun m : Fin n ↦ n - n ≤ (m : ℕ)) = Finset.univ by
    ext m; simp]
  exact Equiv.sum_comp e (fun j ↦ u ⬝ᵥ ((L j * (L j)ᵀ) *ᵥ u))

variable [DecidableEq ι]

/-- A square factor with `Q Qᵀ ≥ c I` (sup-norm form) has `matrixMaxRowAbsSum Q⁻¹ ≤ S / √c`. -/
theorem matrixMaxRowAbsSum_inv_le_of_quadForm {Q : Matrix ι ι ℝ} {c : ℝ} (hc : 0 < c)
    (hQ : ∀ u : ι → ℝ, c * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((Q * Qᵀ) *ᵥ u)) (hdet : IsUnit Q.det) :
    matrixMaxRowAbsSum Q⁻¹ ≤ (Fintype.card ι : ℝ) / √c := by
  refine matrixMaxRowAbsSum_le_of_forall (by positivity) fun a ↦ ?_
  set h : ι → ℝ := fun b ↦ if 0 ≤ Q⁻¹ a b then 1 else -1
  have hh : ‖h‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b ↦ by
    simp only [h]; split_ifs <;> simp
  obtain ⟨w, hw, hws⟩ := exists_mulVec_eq_of_quadForm_ge hc hQ h
  have hwQ : w = Q⁻¹ *ᵥ h := by
    rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hsum : ∑ b, |Q⁻¹ a b| = w a := by
    rw [hwQ]
    simp only [Matrix.mulVec, dotProduct, h]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    split_ifs with hb
    · rw [abs_of_nonneg hb, mul_one]
    · rw [abs_of_neg (not_le.1 hb), mul_neg_one]
  rw [hsum]
  have hw2 : w a ^ 2 ≤ ((Fintype.card ι : ℝ) / √c) ^ 2 := by
    calc w a ^ 2 ≤ ∑ j, w j ^ 2 :=
          Finset.single_le_sum (f := fun j ↦ w j ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ a)
      _ ≤ ((Fintype.card ι : ℝ) / √c) ^ 2 * ‖h‖ ^ 2 := hws
      _ ≤ ((Fintype.card ι : ℝ) / √c) ^ 2 * 1 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) hh
      _ = _ := mul_one _
  exact (abs_le_of_sq_le_sq' hw2 (by positivity)).2

/-- **Twin-law shell bound.** Under `ReservoirCond` (with `r₀ ≤ n`, `n > 0`, `c > 0`), the
`ε`-shell of a convex set has twin-law mass `≤ 4 S² (S/√c) ε / √(2π)`. -/
theorem twinLaw_convexShell_le {e : Fin n ≃ κ} {L : κ → Matrix ι ι ℝ} {c : ℝ} {r₀ : ℕ}
    (hres : ReservoirCond e L c r₀) (hr₀ : r₀ ≤ n) (hn : 0 < n) (hc : 0 < c)
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) {ε : ℝ} (hε : 0 ≤ ε) :
    (twinLaw L).real (cthickening ε K ∩ cthickening ε (interior K)ᶜ) ≤
      4 * (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) / √c) * ε / √(2 * π) := by
  set T := twinMat L Finset.univ
  have hpsd : (T * Tᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose T
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨Q, hQ⟩ := exists_mul_transpose_eq_of_posSemidef hpsd
  have hlaw : twinLaw L = (stdGaussianPi ι).map (Q *ᵥ ·) :=
    map_mulVec_stdGaussianPi_eq T Q hQ.symm
  have hq : ∀ u : ι → ℝ, c * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((Q * Qᵀ) *ᵥ u) := by
    rw [hQ]
    exact quadForm_sup_of_euclid hc.le (total_quadForm hres hr₀ hn)
  have hsurj : Function.Surjective (Q *ᵥ ·) := fun h ↦
    let ⟨w, hw, _⟩ := exists_mulVec_eq_of_quadForm_ge hc hq h
    ⟨w, hw⟩
  have hdet : IsUnit Q.det :=
    (Matrix.isUnit_iff_isUnit_det Q).1 (Matrix.mulVec_surjective_iff_isUnit.1 hsurj)
  rw [hlaw]
  refine (map_mulVec_convexShell_le Q hdet hK hε).trans ?_
  have hinv := matrixMaxRowAbsSum_inv_le_of_quadForm hc hq hdet
  have : 0 ≤ 4 * (Fintype.card ι : ℝ) ^ 2 := by positivity
  gcongr

end Reservoir

end StatisticalRL.Probability
