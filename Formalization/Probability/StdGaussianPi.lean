import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The standard Gaussian measure on `ι → ℝ`

Reusable probability infrastructure (intended integration path
`Formalization/Probability/StdGaussianPi.lean`). Pinned Mathlib has no multivariate standard
Gaussian API; `stdGaussianPi ι` is `Measure.pi fun _ ↦ gaussianReal 0 1`, the law of a vector of
i.i.d. `N(0,1)` coordinates (the same measure as in `gaussCov`).

* moments: `integral_apply_stdGaussianPi` (`∫ zᵢ = 0`), `integral_apply_mul_apply_stdGaussianPi`
  (`∫ zᵢ zⱼ = δᵢⱼ`), linear images `integral_mulVec_apply_stdGaussianPi`,
  `integral_mulVec_apply_mul_mulVec_apply_stdGaussianPi` (`∫ (Lz)ᵢ (Lz)ⱼ = (L Lᵀ)ᵢⱼ`);
* integrability: every continuous `g` with `|g z| ≤ C (1 + ‖z‖³)` is integrable
  (`integrable_of_abs_le_one_add_norm_pow_three`); this rules out the junk value `0` of the
  Bochner integral for the test functions used downstream;
* third moment: `integral_abs_pow_three_gaussianReal_le` (`E|z|³ ≤ 12 e^{1/2}`) and
  `integral_norm_pow_three_stdGaussianPi_le` (`∫ ‖z‖³ ≤ |ι| · 12 e^{1/2}`, sup norm);
* stability: `stdGaussianPi_prod_map_add` (`a Z + b Z' =ᵈ √(a²+b²) Z` for independent standard
  `Z, Z'`, any real `a, b`, zero allowed) and its integral form
  `integral_stdGaussianPi_prod_add`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatisticalRL.Probability

/-- The standard Gaussian measure on `ι → ℝ`: i.i.d. `N(0,1)` coordinates. -/
noncomputable abbrev stdGaussianPi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι ↦ gaussianReal 0 1

variable {ι : Type*} [Fintype ι]

/-! ## One-dimensional facts -/

theorem integral_sq_gaussianReal_zero_one : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 1)
    aemeasurable_id (by simp)
  rw [variance_id_gaussianReal] at h
  simpa using h.symm

theorem integrable_abs_pow_gaussianReal (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simpa [Real.norm_eq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) n).integrable_norm_pow hn.ne'

theorem integrable_pow_gaussianReal (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) := by
  refine (integrable_abs_pow_gaussianReal n).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  simp

/-- `E|z|³ ≤ 12 e^{1/2}` for `z ∼ N(0,1)` (from `|x|³ ≤ 6 e^{|x|} ≤ 6 (eˣ + e⁻ˣ)`). -/
theorem integral_abs_pow_three_gaussianReal_le :
    ∫ x, |x| ^ 3 ∂(gaussianReal 0 1) ≤ 12 * exp (1 / 2) := by
  have hexp : ∀ t : ℝ, ∫ x, exp (t * x) ∂(gaussianReal 0 1) = exp (t ^ 2 / 2) := by
    intro t
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
    simpa [mgf] using this
  have hpt : ∀ x : ℝ, |x| ^ 3 ≤ 6 * (exp (1 * x) + exp ((-1) * x)) := by
    intro x
    have h1 := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) 3
    have h2 : exp |x| ≤ exp (1 * x) + exp ((-1) * x) := by
      rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h, one_mul]; linarith [exp_pos ((-1) * x)]
      · rw [h, neg_one_mul]; linarith [exp_pos (1 * x)]
    norm_num [Nat.factorial] at h1
    linarith
  calc ∫ x, |x| ^ 3 ∂(gaussianReal 0 1)
      ≤ ∫ x, 6 * (exp (1 * x) + exp ((-1) * x)) ∂(gaussianReal 0 1) :=
        integral_mono (integrable_abs_pow_gaussianReal 3)
          (((integrable_exp_mul_gaussianReal 1).add
            (integrable_exp_mul_gaussianReal (-1))).const_mul 6) hpt
    _ = 12 * exp (1 / 2) := by
        rw [integral_const_mul, integral_add (integrable_exp_mul_gaussianReal 1)
          (integrable_exp_mul_gaussianReal (-1)), hexp, hexp]
        norm_num; ring

/-! ## Coordinates -/

theorem measurePreserving_eval_stdGaussianPi (i : ι) :
    MeasurePreserving (Function.eval i) (stdGaussianPi ι) (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i

theorem integrable_apply_comp_stdGaussianPi {g : ℝ → ℝ} (hg : Integrable g (gaussianReal 0 1))
    (i : ι) : Integrable (fun z : ι → ℝ ↦ g (z i)) (stdGaussianPi ι) :=
  (measurePreserving_eval_stdGaussianPi i).integrable_comp_of_integrable hg

theorem integral_apply_comp_stdGaussianPi {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianReal 0 1)) (i : ι) :
    ∫ z, g (z i) ∂(stdGaussianPi ι) = ∫ x, g x ∂(gaussianReal 0 1) := by
  rw [← (measurePreserving_eval_stdGaussianPi i).map_eq] at hg ⊢
  exact (integral_map (measurable_pi_apply i).aemeasurable hg).symm

theorem integrable_abs_apply_pow_stdGaussianPi (i : ι) (n : ℕ) :
    Integrable (fun z : ι → ℝ ↦ |z i| ^ n) (stdGaussianPi ι) :=
  integrable_apply_comp_stdGaussianPi (integrable_abs_pow_gaussianReal n) i

theorem integrable_apply_stdGaussianPi (i : ι) :
    Integrable (fun z : ι → ℝ ↦ z i) (stdGaussianPi ι) :=
  integrable_apply_comp_stdGaussianPi (by simpa using integrable_pow_gaussianReal 1) i

theorem integral_apply_stdGaussianPi (i : ι) : ∫ z, z i ∂(stdGaussianPi ι) = 0 := by
  rw [integral_apply_comp_stdGaussianPi (g := fun x ↦ x) aestronglyMeasurable_id i]
  exact integral_id_gaussianReal

/-- `∫ zᵢ zⱼ = δᵢⱼ` under the standard Gaussian on `ι → ℝ`. -/
theorem integral_apply_mul_apply_stdGaussianPi [DecidableEq ι] (i j : ι) :
    ∫ z, z i * z j ∂(stdGaussianPi ι) = if i = j then 1 else 0 := by
  set g : ι → ℝ → ℝ := fun k x ↦ (if k = i then x else 1) * (if k = j then x else 1)
  have hprod : ∀ z : ι → ℝ, ∏ k, g k (z k) = z i * z j := by
    intro z
    simp only [g, Finset.prod_mul_distrib]
    simp
  have hint := integral_fintype_prod_eq_prod (𝕜 := ℝ) g (μ := fun _ : ι ↦ gaussianReal 0 1)
  simp only [hprod] at hint
  rw [hint]
  have h1 : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  split_ifs with hij
  · subst hij
    refine Finset.prod_eq_one fun k _ ↦ ?_
    by_cases hk : k = i
    · simp only [g, hk, if_true]
      simpa [sq] using integral_sq_gaussianReal_zero_one
    · simp [g, hk]
  · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [g, hij, h1]

/-! ## Norms and integrability -/

theorem norm_pow_three_le_sum (z : ι → ℝ) : ‖z‖ ^ 3 ≤ ∑ i, |z i| ^ 3 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim z 0]
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |z i|) Finset.univ_nonempty
  have hz : ‖z‖ ≤ |z i| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun k ↦ by
      simpa [Real.norm_eq_abs] using hi k (Finset.mem_univ k)
  calc ‖z‖ ^ 3 ≤ |z i| ^ 3 := pow_le_pow_left₀ (norm_nonneg z) hz 3
    _ ≤ ∑ k, |z k| ^ 3 :=
        Finset.single_le_sum (f := fun k ↦ |z k| ^ 3) (fun k _ ↦ by positivity)
          (Finset.mem_univ i)

theorem integrable_norm_pow_three_stdGaussianPi :
    Integrable (fun z : ι → ℝ ↦ ‖z‖ ^ 3) (stdGaussianPi ι) := by
  refine (integrable_finset_sum Finset.univ fun i _ ↦
    integrable_abs_apply_pow_stdGaussianPi i 3).mono' (by fun_prop) (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa using norm_pow_three_le_sum z

/-- `∫ ‖z‖³ ≤ |ι| · 12 e^{1/2}` (sup norm). -/
theorem integral_norm_pow_three_stdGaussianPi_le :
    ∫ z, ‖z‖ ^ 3 ∂(stdGaussianPi ι) ≤ Fintype.card ι * (12 * exp (1 / 2)) := by
  calc ∫ z, ‖z‖ ^ 3 ∂(stdGaussianPi ι) ≤ ∫ z, ∑ i, |z i| ^ 3 ∂(stdGaussianPi ι) :=
        integral_mono integrable_norm_pow_three_stdGaussianPi
          (integrable_finset_sum Finset.univ fun i _ ↦ integrable_abs_apply_pow_stdGaussianPi i 3)
          norm_pow_three_le_sum
    _ = ∑ i : ι, ∫ x, |x| ^ 3 ∂(gaussianReal 0 1) := by
        rw [integral_finset_sum Finset.univ fun i _ ↦ integrable_abs_apply_pow_stdGaussianPi i 3]
        exact Finset.sum_congr rfl fun i _ ↦ integral_apply_comp_stdGaussianPi
          (g := fun x ↦ |x| ^ 3) (by fun_prop : Continuous fun x : ℝ ↦ |x| ^ 3).aestronglyMeasurable i
    _ ≤ ∑ _i : ι, 12 * exp (1 / 2) :=
        Finset.sum_le_sum fun _ _ ↦ integral_abs_pow_three_gaussianReal_le
    _ = Fintype.card ι * (12 * exp (1 / 2)) := by simp

theorem pow_le_one_add_pow_three {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≤ 3) :
    x ^ k ≤ 1 + x ^ 3 := by
  rcases le_or_gt x 1 with h | h
  · have := pow_le_one₀ hx h (n := k)
    have : 0 ≤ x ^ 3 := by positivity
    linarith
  · have := pow_le_pow_right₀ h.le hk
    linarith

/-- A continuous function with at most cubic growth is integrable for the standard Gaussian. -/
theorem integrable_of_abs_le_one_add_norm_pow_three {g : (ι → ℝ) → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ z, |g z| ≤ C * (1 + ‖z‖ ^ 3)) : Integrable g (stdGaussianPi ι) := by
  refine ((integrable_const 1).add integrable_norm_pow_three_stdGaussianPi |>.const_mul C).mono'
    hg.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  simpa [Real.norm_eq_abs] using hC z

/-! ## Linear images -/

theorem abs_apply_le_norm (z : ι → ℝ) (i : ι) : |z i| ≤ ‖z‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm z i

theorem integrable_apply_mul_apply_stdGaussianPi (i j : ι) :
    Integrable (fun z : ι → ℝ ↦ z i * z j) (stdGaussianPi ι) := by
  refine integrable_of_abs_le_one_add_norm_pow_three (by fun_prop) (C := 1) fun z ↦ ?_
  have hi := abs_apply_le_norm z i
  have hj := abs_apply_le_norm z j
  have h2 := pow_le_one_add_pow_three (norm_nonneg z) (k := 2) (by norm_num)
  rw [abs_mul, one_mul]
  calc |z i| * |z j| ≤ ‖z‖ * ‖z‖ :=
        mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
    _ = ‖z‖ ^ 2 := by ring
    _ ≤ 1 + ‖z‖ ^ 3 := h2

theorem integral_mulVec_apply_stdGaussianPi (L : Matrix ι ι ℝ) (i : ι) :
    ∫ z, (L.mulVec z) i ∂(stdGaussianPi ι) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [integral_finset_sum _ fun k _ ↦ (integrable_apply_stdGaussianPi k).const_mul _]
  simp [integral_const_mul, integral_apply_stdGaussianPi]

/-- `∫ (Lz)ᵢ (Lz)ⱼ = (L Lᵀ)ᵢⱼ` under the standard Gaussian. -/
theorem integral_mulVec_apply_mul_mulVec_apply_stdGaussianPi [DecidableEq ι]
    (L : Matrix ι ι ℝ) (i j : ι) :
    ∫ z, (L.mulVec z) i * (L.mulVec z) j ∂(stdGaussianPi ι) = (L * L.transpose) i j := by
  have e : ∀ z : ι → ℝ, (L.mulVec z) i * (L.mulVec z) j =
      ∑ k, ∑ l, L i k * L j l * (z k * z l) := by
    intro z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    ring
  simp_rw [e]
  rw [integral_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
    (integrable_apply_mul_apply_stdGaussianPi k l).const_mul _]
  simp_rw [integral_finset_sum _ fun l _ ↦
    (integrable_apply_mul_apply_stdGaussianPi _ l).const_mul _, integral_const_mul,
    integral_apply_mul_apply_stdGaussianPi]
  simp [Matrix.mul_apply]

/-! ## Stability under independent sums -/

/-- One-dimensional stability: `a X + b Y ∼ N(0, a² + b²)` for independent `X, Y ∼ N(0,1)`. -/
theorem gaussianReal_prod_map_add (a b : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ ↦ a * p.1 + b * p.2) =
      gaussianReal 0 ⟨a ^ 2 + b ^ 2, by positivity⟩ := by
  have hmap : (fun p : ℝ × ℝ ↦ a * p.1 + b * p.2) =
      (fun p : ℝ × ℝ ↦ p.1 + p.2) ∘ Prod.map (a * ·) (b * ·) := rfl
  rw [hmap, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_mul]
  have := gaussianReal_conv_gaussianReal (m₁ := a * 0) (m₂ := b * 0)
    (v₁ := ⟨a ^ 2, sq_nonneg _⟩ * 1) (v₂ := ⟨b ^ 2, sq_nonneg _⟩ * 1)
  rw [Measure.conv] at this
  rw [this]
  congr 1
  · simp
  · ext; simp

/-- Stability of the standard Gaussian on `ι → ℝ`: for independent standard `Z, Z'` and any real
`a, b` (zero allowed), `a Z + b Z'` has the law of `√(a² + b²) Z`. -/
theorem stdGaussianPi_prod_map_add (a b : ℝ) :
    ((stdGaussianPi ι).prod (stdGaussianPi ι)).map
        (fun p : (ι → ℝ) × (ι → ℝ) ↦ a • p.1 + b • p.2) =
      (stdGaussianPi ι).map (fun z ↦ √(a ^ 2 + b ^ 2) • z) := by
  have hmp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ ↦ gaussianReal 0 1)
    (fun _ ↦ gaussianReal 0 1)).map_eq
  rw [← hmp, Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  have h1 : ((fun p : (ι → ℝ) × (ι → ℝ) ↦ a • p.1 + b • p.2) ∘
      MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι) =
      fun q : ι → ℝ × ℝ ↦ fun i ↦ (fun p : ℝ × ℝ ↦ a * p.1 + b * p.2) (q i) := by
    ext q i
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  have h2 : (fun z : ι → ℝ ↦ √(a ^ 2 + b ^ 2) • z) =
      fun z : ι → ℝ ↦ fun i ↦ (fun x : ℝ ↦ √(a ^ 2 + b ^ 2) * x) (z i) := by
    ext z i; simp
  rw [h1, h2, Measure.pi_map_pi (f := fun _ (p : ℝ × ℝ) ↦ a * p.1 + b * p.2)
    (fun _ ↦ by fun_prop), Measure.pi_map_pi (f := fun _ (x : ℝ) ↦ √(a ^ 2 + b ^ 2) * x)
    (fun _ ↦ by fun_prop)]
  congr 1
  ext1 i
  rw [gaussianReal_prod_map_add, gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2)]

/-- Integral form of `stdGaussianPi_prod_map_add`: for measurable `F` with
`z ↦ F (√(a²+b²) z)` integrable, `(Z, Z') ↦ F (a Z + b Z')` is integrable on the product and has the
same integral. -/
theorem integral_stdGaussianPi_prod_add (a b : ℝ) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    (hint : Integrable (fun z ↦ F (√(a ^ 2 + b ^ 2) • z)) (stdGaussianPi ι)) :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) ↦ F (a • p.1 + b • p.2))
        ((stdGaussianPi ι).prod (stdGaussianPi ι)) ∧
      ∫ p, F (a • p.1 + b • p.2) ∂((stdGaussianPi ι).prod (stdGaussianPi ι)) =
        ∫ z, F (√(a ^ 2 + b ^ 2) • z) ∂(stdGaussianPi ι) := by
  have hφ : Measurable (fun p : (ι → ℝ) × (ι → ℝ) ↦ a • p.1 + b • p.2) := by fun_prop
  have hψ : Measurable (fun z : ι → ℝ ↦ √(a ^ 2 + b ^ 2) • z) := by fun_prop
  have hmap := stdGaussianPi_prod_map_add (ι := ι) a b
  have hFi : Integrable F ((stdGaussianPi ι).map (fun z ↦ √(a ^ 2 + b ^ 2) • z)) :=
    (integrable_map_measure hF.aestronglyMeasurable hψ.aemeasurable).2 hint
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hFi
    exact (integrable_map_measure hF.aestronglyMeasurable hφ.aemeasurable).1 hFi
  · rw [← integral_map hφ.aemeasurable hF.aestronglyMeasurable, hmap,
      integral_map hψ.aemeasurable hF.aestronglyMeasurable]

end StatisticalRL.Probability
