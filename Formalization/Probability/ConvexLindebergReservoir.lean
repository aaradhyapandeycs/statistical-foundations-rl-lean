import Formalization.Probability.ConvexLindebergReservoirBase
import Formalization.Probability.GaussianBlock
import Formalization.Analysis.InvSqrtTelescope

/-!
# Reservoir Lindeberg swap, pass 1: multivariate convex Berry–Esseen at `n^{-1/4}`

Infrastructure only; this is a planner/P0 construction (Lindeberg replacement with a Gaussian
reservoir and Bentkus-type smoothing of convex indicators), not a result taken from a cited paper
and not a source result of the formalized monograph. In particular it is not Theorem 7.11.

Setting: independent summands `Y i (ω i)` with finite laws `p i` (the product expectation
`Stein.pexp`), centred, with covariances `L i (L i)ᵀ` and sup norms at most `B / √n`. Their Gaussian
twins `L i w_i` share one standard Gaussian vector `w : κ × ι → ℝ`. If the twins satisfy the
reservoir condition `ReservoirCond e L c r₀` along the swap order `e`, then for every convex set `K`
(measurable or not)

  `|P(∑ᵢ Yᵢ ∈ K) − N(0, ∑ᵢ Lᵢ Lᵢᵀ)(K)| ≤ reservoirQuarterConst ι c r₀ B · n^{-1/4}`

(`abs_pexp_convex_sub_twinLaw_le_quarter`), with a constant depending only on `|ι|`, `c`, `r₀`, `B`.

Proof outline: the hybrids `H_k` replace the twins one at a time (`hexp`). The step at `k` is
bounded by smoothing with the remaining Gaussian reservoir when it is large (covariance
`≥ c (n-1-k)/n · I`, Gaussian smoothing derivative bounds), and by the third derivative of the test
function otherwise; the step costs telescope to `O(n^{-1/4})` for tests at scale `ε = n^{-1/4}`
(`abs_pexp_sub_twinLaw_le_smooth`). The smoothing inequality and the Gaussian shell bound of the
twin law then pass to indicators of convex sets.
-/

open MeasureTheory ProbabilityTheory Real Matrix Metric
open StatisticalRL.Analysis

namespace StatisticalRL.Probability

section Steps

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] {n : ℕ}

/-- The Gaussian-side step: integrating out the twin block of index `e k`. -/
theorem hexp_eq_integral_block (p : ∀ i, X i → ℝ) (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ)
    (L : κ → Matrix ι ι ℝ) {f : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {k : ℕ} (hk : k < n) :
    hexp p e Y L f k = Stein.pexp p (fun ω ↦ ∫ z, ∫ w,
      f (prefixSum e Y k ω + L (e ⟨k, hk⟩) *ᵥ z + twinMat L (resSet e k) *ᵥ w)
        ∂stdGaussianPi (κ × ι) ∂stdGaussianPi ι) := by
  unfold hexp
  congr 1; funext ω
  simp only [hybrid_eq e Y L hk]
  refine integral_comp_blockOf_indep (e ⟨k, hk⟩)
    (G := fun z w ↦ f (prefixSum e Y k ω + L (e ⟨k, hk⟩) *ᵥ z + twinMat L (resSet e k) *ᵥ w))
    ?_ (C := 1) ?_ ?_
  · exact hf.comp ((continuous_const.add ((continuous_mulVec_const _).comp continuous_fst)).add
      ((continuous_mulVec_const _).comp continuous_snd))
  · intro z w
    have h := hf01 (prefixSum e Y k ω + L (e ⟨k, hk⟩) *ᵥ z + twinMat L (resSet e k) *ᵥ w)
    rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
  · intro z w w'
    simp only
    rw [twinMat_mulVec_congr L (resSet e k) (w := blockPw (e ⟨k, hk⟩) w' w) (w' := w)
      (fun j hj a ↦ ?_)]
    rw [blockPw_apply, if_neg]
    rintro rfl
    exact not_mem_resSet e hk hj

/-- **One hybrid step.** A pointwise bound `C` on the one-step swap, uniform in the base point,
bounds `|E φ(H_{k+1}) − E φ(H_k)|`. -/
theorem abs_hexp_succ_sub_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Continuous f) (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {k : ℕ}
    (hk : k < n) {C : ℝ}
    (hC : ∀ U : ι → ℝ, |∑ y, p (e ⟨k, hk⟩) y *
        ∫ w, f (U + Y (e ⟨k, hk⟩) y + twinMat L (resSet e k) *ᵥ w) ∂stdGaussianPi (κ × ι) -
      ∫ z, ∫ w, f (U + L (e ⟨k, hk⟩) *ᵥ z + twinMat L (resSet e k) *ᵥ w)
        ∂stdGaussianPi (κ × ι) ∂stdGaussianPi ι| ≤ C) :
    |hexp p e Y L f (k + 1) - hexp p e Y L f k| ≤ C := by
  rw [hexp_succ_eq hp1 e Y L f hk, hexp_eq_integral_block p e Y L hf hf01 hk, ← Stein.pexp_sub]
  refine (Stein.abs_pexp_le hp0 _).trans ?_
  exact (Stein.pexp_mono hp0 fun ω ↦ hC _).trans_eq (Stein.pexp_const hp1 C)

end Steps

/-! ## Telescoping for smooth tests -/

/-- `(v √v)⁻¹ b³` for `v = c j / n` and `b = B / √n`. -/
theorem reservoir_step_const_eq {c B : ℝ} (hc : 0 < c) {n j : ℕ} (hn : 0 < n) (hj : 0 < j) :
    ((c * (j : ℝ) / n) * √(c * (j : ℝ) / n))⁻¹ * (B / √(n : ℝ)) ^ 3 =
      (c * √c)⁻¹ * B ^ 3 * ((j : ℝ) * √(j : ℝ))⁻¹ := by
  have hN : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsj : 0 < √(j : ℝ) := Real.sqrt_pos.2 hj0
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hc.le]
  set s := √(n : ℝ)
  rw [hN]
  field_simp

/-- The reservoir smoothing constant `gaussDerivConst 3 · |ι|³`. -/
noncomputable def reservoirHermiteConst (ι : Type*) [Fintype ι] : ℝ :=
  gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3

theorem reservoirHermiteConst_nonneg (ι : Type*) [Fintype ι] : 0 ≤ reservoirHermiteConst ι := by
  unfold reservoirHermiteConst; have := gaussDerivConst_nonneg 3; positivity

section Telescope

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **Smooth-test comparison (telescoping).** For every `C^∞` test `φ` with values in `[0,1]` and
`‖Dᵏ φ‖ ≤ sandwichConst ι k / εᵏ` at the scale `ε = n^{-1/4}`, the sum of independent bounded
centred summands under `ReservoirCond` satisfies
`|E φ(∑ Y) − ∫ φ d twinLaw| ≤ A₃ B³/6 · (c₃ (2 + r₀) + 4 C_H (c √c)⁻¹) · n^{-1/4}`. -/
theorem abs_pexp_sub_twinLaw_le_smooth {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hres : ReservoirCond e L c r₀)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ (k : ℕ) (x : ι → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤
      ConvexSmoothIndicator.sandwichConst ι k / ((√√(n : ℝ))⁻¹) ^ k) :
    |Stein.pexp p (fun ω ↦ φ (∑ i, Y i (ω i))) - ∫ y, φ y ∂(twinLaw L)| ≤
      lindebergMomentConst ι * B ^ 3 / 6 *
        (ConvexSmoothIndicator.sandwichConst ι 3 * (2 + r₀) +
          4 * reservoirHermiteConst ι * (c * √c)⁻¹) / √√(n : ℝ) := by
  have hb0 : 0 ≤ B / √(n : ℝ) := by positivity
  have htel : Stein.pexp p (fun ω ↦ φ (∑ i, Y i (ω i))) - ∫ y, φ y ∂(twinLaw L) =
      ∑ k ∈ Finset.range n, (hexp p e Y L φ (k + 1) - hexp p e Y L φ k) := by
    rw [Finset.sum_range_sub (fun k ↦ hexp p e Y L φ k), hexp_n, hexp_zero hp1 e Y L hφ.continuous]
  rw [htel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine sum_range_le_quarter hn r₀ (ConvexSmoothIndicator.sandwichConst_nonneg 3)
    (reservoirHermiteConst_nonneg ι) lindebergMomentConst_nonneg hB hc.le
    (a := fun k ↦ |hexp p e Y L φ (k + 1) - hexp p e Y L φ k|) ?_ ?_
  · intro k hk hJ
    have hceil : 0 < ⌈√(n : ℝ)⌉₊ := Nat.ceil_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))
    have hj : 0 < n - 1 - k := by omega
    have hv0 : 0 < c * ((n - 1 - k : ℕ) : ℝ) / n := by
      have : (0 : ℝ) < ((n - 1 - k : ℕ) : ℝ) := by exact_mod_cast hj
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hv := reservoir_quadForm hres hk (by omega)
    refine abs_hexp_succ_sub_le hp0 hp1 e Y L hφ.continuous h01 hk fun U ↦ ?_
    refine (abs_step_le_of_reservoir (hp0 _) (hp1 _) (hmean _) (hcov _) hb0 (hb _) hφ h01
      (fun j ↦ ⟨_, hd j⟩) _ hv0 hv U).trans (le_of_eq ?_)
    have := reservoir_step_const_eq (B := B) hc hn hj
    unfold reservoirHermiteConst
    calc gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 *
            ((c * ((n - 1 - k : ℕ) : ℝ) / n) * √(c * ((n - 1 - k : ℕ) : ℝ) / n))⁻¹ / 6 *
          (lindebergMomentConst ι * (B / √(n : ℝ)) ^ 3)
        = gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 / 6 * lindebergMomentConst ι *
          (((c * ((n - 1 - k : ℕ) : ℝ) / n) * √(c * ((n - 1 - k : ℕ) : ℝ) / n))⁻¹ *
            (B / √(n : ℝ)) ^ 3) := by ring
      _ = _ := by rw [this]; ring
  · intro k hk _
    refine abs_hexp_succ_sub_le hp0 hp1 e Y L hφ.continuous h01 hk fun U ↦ ?_
    refine (abs_step_le_of_sandwich (hp0 _) (hp1 _) (hmean _) (hcov _) hb0 (hb _) hφ h01 hd
      _ U).trans (le_of_eq ?_)
    rw [inv_pow, div_inv_eq_mul]
    ring

end Telescope

/-! ## Main theorem -/

/-- The constant of the pass-1 bound:
`4 S² (S/√c)/√(2π) + A₃ B³/6 · (sandwichConst ι 3 · (2 + r₀) + 4 · gaussDerivConst 3 · S³ · (c √c)⁻¹)`. -/
noncomputable def reservoirQuarterConst (ι : Type*) [Fintype ι] (c : ℝ) (r₀ : ℕ) (B : ℝ) : ℝ :=
  4 * (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) / √c) / √(2 * π) +
    lindebergMomentConst ι * B ^ 3 / 6 *
      (ConvexSmoothIndicator.sandwichConst ι 3 * (2 + r₀) +
        4 * reservoirHermiteConst ι * (c * √c)⁻¹)

theorem rpow_neg_quarter_eq (n : ℕ) : (n : ℝ) ^ (-(1 / 4 : ℝ)) = (√√(n : ℝ))⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

section Main

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

instance isProbabilityMeasure_twinLaw (L : κ → Matrix ι ι ℝ) :
    IsProbabilityMeasure (twinLaw L) :=
  Measure.isProbabilityMeasure_map (continuous_mulVec_const _).measurable.aemeasurable

/-- **Reservoir Lindeberg, pass 1** (infrastructure; planner/P0 construction, not a cited result).
Independent bounded centred summands with finite laws whose Gaussian twins satisfy `ReservoirCond`
are within `reservoirQuarterConst · n^{-1/4}` of their twin Gaussian law, uniformly over all convex
sets (measurable or not). -/
theorem abs_pexp_convex_sub_twinLaw_le_quarter {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hr₀ : r₀ ≤ n) (hres : ReservoirCond e L c r₀)
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    |Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (∑ i, Y i (ω i))) - (twinLaw L).real K| ≤
      reservoirQuarterConst ι c r₀ B * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have ht : 0 < √√(n : ℝ) := Real.sqrt_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hε : 0 < (√√(n : ℝ))⁻¹ := inv_pos.2 ht
  have h := abs_pexp_indicator_sub_le_of_smooth hp0 (fun ω ↦ ∑ i, Y i (ω i)) (twinLaw L) hε K
    (twinLaw_convexShell_le hres hr₀ hn hc hK hε.le)
    (fun φ hφ h01 hd ↦ abs_pexp_sub_twinLaw_le_smooth e hn hp0 hp1 hmean hcov hB hb hc hres hφ
      h01 hd)
  refine h.trans (le_of_eq ?_)
  rw [rpow_neg_quarter_eq, reservoirQuarterConst]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The law of `Z` under the product weights evaluated on a measurable set. -/
theorem lawPexp_real_eq {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) (Z : (∀ i, X i) → ι → ℝ)
    {K : Set (ι → ℝ)} (hK : MeasurableSet K) :
    (lawPexp p Z).real K = Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) := by
  rw [measureReal_def, lawPexp, Measure.coe_finset_sum, Finset.sum_apply,
    ENNReal.toReal_sum fun ω _ ↦ by
      rw [Measure.smul_apply, Measure.dirac_apply' _ hK, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by by_cases h : Z ω ∈ K <;> simp [h])]
  unfold Stein.pexp
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hK, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Stein.prod_weight_nonneg hp0 ω)]
  by_cases h : Z ω ∈ K <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem cvxDist_le_of_forall {μ ν : Measure (ι → ℝ)} {C : ℝ}
    (h : ∀ K, Convex ℝ K → MeasurableSet K → |μ.real K - ν.real K| ≤ C) : cvxDist μ ν ≤ C := by
  haveI : Nonempty {K : Set (ι → ℝ) // Convex ℝ K ∧ MeasurableSet K} :=
    ⟨⟨∅, convex_empty, MeasurableSet.empty⟩⟩
  exact ciSup_le fun K ↦ h K.1 K.2.1 K.2.2

omit [Fintype ι] [DecidableEq ι] in
theorem le_cvxDist {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) (hKm : MeasurableSet K) :
    |μ.real K - ν.real K| ≤ cvxDist μ ν := by
  refine le_ciSup (f := fun K : {K : Set (ι → ℝ) // Convex ℝ K ∧ MeasurableSet K} ↦
    |μ.real K.1 - ν.real K.1|) ⟨μ.real Set.univ + ν.real Set.univ, ?_⟩ ⟨K, hK, hKm⟩
  rintro _ ⟨K', rfl⟩
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
  exact add_le_add (measureReal_mono (Set.subset_univ _)) (measureReal_mono (Set.subset_univ _))

/-- Convex-distance form of the pass-1 bound. -/
theorem cvxDist_lawPexp_twinLaw_le_quarter {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hr₀ : r₀ ≤ n) (hres : ReservoirCond e L c r₀) :
    cvxDist (lawPexp p (fun ω ↦ ∑ i, Y i (ω i))) (twinLaw L) ≤
      reservoirQuarterConst ι c r₀ B * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
  cvxDist_le_of_forall fun K hK hKm ↦ by
    rw [lawPexp_real_eq hp0 _ hKm]
    exact abs_pexp_convex_sub_twinLaw_le_quarter e hn hp0 hp1 hmean hcov hB hb hc hr₀ hres hK

end Main

/-! ## Non-vacuity: scaled Rademacher summands at every `n ≥ 1` -/

section NonVacuity

/-- Scaled Rademacher summand `±(√n)⁻¹` on `Fin 1`. -/
noncomputable def radSummand (n : ℕ) (_i : Fin n) (x : Bool) : Fin 1 → ℝ :=
  fun _ ↦ if x then (√(n : ℝ))⁻¹ else -(√(n : ℝ))⁻¹

/-- Its covariance factor `(√n)⁻¹ • 1`. -/
noncomputable def radFactor (n : ℕ) (_i : Fin n) : Matrix (Fin 1) (Fin 1) ℝ :=
  (√(n : ℝ))⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ)

theorem radFactor_mul_transpose (n : ℕ) (i : Fin n) :
    radFactor n i * (radFactor n i)ᵀ = ((√(n : ℝ))⁻¹ ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  simp [radFactor, smul_smul, sq]

theorem reservoirCond_rad {n : ℕ} (hn : 0 < n) :
    ReservoirCond (Equiv.refl (Fin n)) (radFactor n) 1 0 := by
  intro r _ hr u
  have hcard : (Finset.univ.filter fun m : Fin n ↦ n - r ≤ (m : ℕ)).card = r := by
    have : (Finset.univ.filter fun m : Fin n ↦ n - r ≤ (m : ℕ)).map Fin.valEmbedding =
        Finset.Ico (n - r) n := by
      ext m
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨m', hm', rfl⟩; exact ⟨hm', m'.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨m, h2⟩, h1, rfl⟩
    rw [← Finset.card_map, this, Nat.card_Ico]; omega
  simp only [Equiv.refl_apply, radFactor_mul_transpose, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, Finset.sum_const, hcard, nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_pow, Real.sq_sqrt hn'.le]
  apply le_of_eq
  field_simp

/-- **Non-vacuity** of `abs_pexp_convex_sub_twinLaw_le_quarter` at every `n ≥ 1`: `n` scaled
Rademacher signs on `Fin 1`, with `c = 1`, `r₀ = 0`, `B = 1`, satisfy all hypotheses. -/
theorem rad_convex_le_quarter {n : ℕ} (hn : 0 < n) {K : Set (Fin 1 → ℝ)} (hK : Convex ℝ K) :
    |Stein.pexp (fun (_ : Fin n) (_ : Bool) ↦ (1 / 2 : ℝ))
        (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (∑ i, radSummand n i (ω i))) -
      (twinLaw (radFactor n)).real K| ≤
      reservoirQuarterConst (Fin 1) 1 0 1 * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine abs_pexp_convex_sub_twinLaw_le_quarter (Equiv.refl (Fin n)) hn (fun _ _ ↦ by norm_num)
    (fun _ ↦ by simp) ?_ ?_ zero_le_one ?_ one_pos (Nat.zero_le n)
    (reservoirCond_rad hn) hK
  · intro i a
    simp [radSummand]
  · intro i a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0, radFactor_mul_transpose]
    have hs : (√(n : ℝ))⁻¹ ^ 2 = (n : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hn'.le]
    simp [radSummand]
    linear_combination hs
  · intro i x
    rw [one_div]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun _ ↦ ?_
    cases x <;> simp [radSummand, abs_of_pos (Real.sqrt_pos.2 hn')]

end NonVacuity

end StatisticalRL.Probability
