import Formalization.TDInference.PrintedStatement
import Formalization.MDP.PointMassDefinitions
import Formalization.OfflineRL.VILCBDatasetDefinitions

/-!
# Theorem 7.11 is false under the every-`V₀`, `r(s) = r_π(s)` reading: a zero-noise instance
(SOURCE-ISSUES C43, refutation R1)

Reading: rewards depend on `(s,a)` as printed (`inference.tex:62`), the undefined `r(s)` in `Γ` is
`r_π(s)` (`prelim.tex:418`), and the bound must hold for every initialization `V₀`. The reading
with one `V₀` per instance is refuted in `TDInference/AnyInitRefutation.lean`. Not refuted here: the
state-only-reward (or deterministic-`π`) reading, where the printed `Γ` is the true noise
covariance, and the corrected statement with the true `Γ`.

Source: `chapters/inference.tex:132–141` (statement), :99–117 (`A`, `Γ`), :47–90 (algorithm).

Instance Z: two states and two actions, `γ = 1/2`, `μ` and `π` uniform, action `a` leads
deterministically to next state `a`, rewards `r(0,0) = 1/2`, `r(0,1) = 3/4`, `r(1,0) = 0`,
`r(1,1) = 1/4` (all in `[0,1]`). Then `V^π = (1, 1/2)` and `r(s,a) + γV^π(a) = V^π(s)` for
*every* `(s,a)`: the per-sample TD noise vanishes identically, so started from `V₀ = V^π` the TD
iterates never move and `√T Δ̄_T = 0` surely. But the printed `Γ` (with `r(s) = r_π(s)`) is
`diag(1/128, 1/128) ≻ 0` and `A` is invertible, so the printed Gaussian `N(0, A⁻¹ΓA⁻ᵀ)` has no
atom at `0`. On the closed convex set `{0}` the gap is `1` for every `T ≥ 1`, while the printed
right-hand side tends to `0` for any constants `c`, `C̃` (`zeroNoise_violates`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.TemporalDifference (policyReward)
open StatisticalRL.EnvironmentStage (pointMass)
open StatisticalRL.OfflineVILCB (uniformRow)

/-! ## A general fact: the printed-form Gaussian has no atom at the origin -/

/-- If `A` is invertible and `Γ ≻ 0`, then `N(0, A⁻¹ diag(Γ) A⁻ᵀ)` gives `{0}` mass `0`. -/
theorem gaussCov_singleton_zero {State : Type} [Fintype State] [DecidableEq State]
    [Nonempty State] (A : Matrix State State ℝ) (Γ : State → ℝ) (hA : IsUnit A.det)
    (hΓ : ∀ s, 0 < Γ s) : gaussCov A Γ {0} = 0 := by
  unfold gaussCov
  rw [Measure.map_apply (measurable_gaussMap A Γ) (measurableSet_singleton 0)]
  have hsub : gaussMap A Γ ⁻¹' {0} ⊆ Set.univ.pi (fun _ : State ↦ ({0} : Set ℝ)) := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    have hw : (fun s ↦ Real.sqrt (Γ s) * z s) = 0 := by
      have h := congrArg (Matrix.mulVec A) hz
      rwa [gaussMap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h
    intro s _
    have h := congrFun hw s
    simp only [Pi.zero_apply, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Real.sqrt_pos.2 (hΓ s)).ne'
    · exact h
  refine measure_mono_null hsub ?_
  rw [Measure.pi_pi]
  obtain ⟨s⟩ := ‹Nonempty State›
  haveI := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact Finset.prod_eq_zero (Finset.mem_univ s) (measure_singleton 0)

theorem gaussCov_real_singleton_zero {State : Type} [Fintype State] [DecidableEq State]
    [Nonempty State] (A : Matrix State State ℝ) (Γ : State → ℝ) (hA : IsUnit A.det)
    (hΓ : ∀ s, 0 < Γ s) : (gaussCov A Γ).real {0} = 0 := by
  simp [Measure.real, gaussCov_singleton_zero A Γ hA hΓ]

/-! ## Instance Z -/

namespace ZeroNoise

/-- The MDP of instance Z: action `a` moves deterministically to state `a`. -/
noncomputable def zMDP : DiscountedMDP (Fin 2) (Fin 2) where
  state_nonempty := ⟨0⟩
  action_nonempty := ⟨0⟩
  transition _ a := pointMass a
  reward := ![![1 / 2, 3 / 4], ![0, 1 / 4]]
  reward_nonneg s a := by fin_cases s <;> fin_cases a <;> norm_num
  reward_le_one s a := by fin_cases s <;> fin_cases a <;> norm_num
  discount := 1 / 2
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- The uniform policy. -/
noncomputable def zPolicy : StationaryPolicy (Fin 2) (Fin 2) := fun _ ↦ uniformRow (Fin 2)

/-- The uniform sampling distribution `μ`. -/
noncomputable def zMu : FiniteDistribution (Fin 2) := uniformRow (Fin 2)

/-- `V^π = (1, 1/2)`. -/
noncomputable def zV : Fin 2 → ℝ := ![1, 1 / 2]

theorem uniformRow_two_prob (x : Fin 2) : (uniformRow (Fin 2)).prob x = 1 / 2 := by
  norm_num [uniformRow]

theorem zTransition_prob (s a t : Fin 2) :
    (zMDP.transition s a).prob t = if t = a then 1 else 0 := by
  simp only [zMDP, pointMass]
  split_ifs <;> rfl

theorem zPolicyTransition_prob (s t : Fin 2) : (zMDP.policyTransition zPolicy s).prob t = 1 / 2 := by
  rw [DiscountedMDP.policyTransition_prob]
  simp only [FiniteDistribution.expectation, Fin.sum_univ_two, zPolicy, uniformRow_two_prob,
    zTransition_prob]
  fin_cases t <;> norm_num

/-- The TD noise vanishes: `r(s,a) + γV^π(a) = V^π(s)` for every `(s,a)`. -/
theorem zReward_bellman (s a : Fin 2) : zMDP.reward s a + zMDP.discount * zV a = zV s := by
  fin_cases s <;> fin_cases a <;> norm_num [zMDP, zV]

theorem zValueFixedPoint : zMDP.valueFixedPoint zPolicy = zV := by
  refine ((zMDP.valueFixedPoint_characterization zPolicy zV).1 ?_).symm
  funext s
  simp only [DiscountedMDP.valueBellman, FiniteDistribution.expectation, Fin.sum_univ_two,
    zPolicyTransition_prob, zPolicy, uniformRow_two_prob]
  fin_cases s <;> norm_num [zMDP, zV]

theorem zPolicyReward (s : Fin 2) :
    policyReward zMDP zPolicy s = ![5 / 8, 1 / 8] s := by
  simp only [policyReward, FiniteDistribution.expectation, Fin.sum_univ_two, zPolicy,
    uniformRow_two_prob]
  fin_cases s <;> norm_num [zMDP]

theorem zMu_pos (s : Fin 2) : 0 < zMu.prob s := by
  rw [zMu, uniformRow_two_prob]; norm_num

/-- The printed `Γ = diag(1/128, 1/128)`. -/
theorem zPrintedGamma (s : Fin 2) : printedGamma zMDP zPolicy zMu s = 1 / 128 := by
  simp only [printedGamma, FiniteDistribution.expectation, Fin.sum_univ_two,
    zPolicyTransition_prob, zValueFixedPoint, zPolicyReward, zMu, uniformRow_two_prob]
  fin_cases s <;> norm_num [zMDP, zV]

theorem zPrintedGamma_pos (s : Fin 2) : 0 < printedGamma zMDP zPolicy zMu s := by
  rw [zPrintedGamma]; norm_num

/-- The printed coefficient at instance Z is an honest positive real number
(`λ₀ = 1/2`, `Tr Γ ‖Γ⁻¹‖ = 2`, `κ(Γ) = 1`, `S = 2`): `K = 2√(4η₀) + 4√2/η₀` for `η₀ > 0`. -/
theorem zPrintedRate_pos {η₀ : ℝ} (hη₀ : 0 < η₀) :
    0 < printedRate zMDP zMu (printedGamma zMDP zPolicy zMu) η₀ := by
  have hΓ : printedGamma zMDP zPolicy zMu = fun _ ↦ 1 / 128 := funext zPrintedGamma
  have hμ : zMu.prob = fun _ ↦ 1 / 2 := funext uniformRow_two_prob
  rw [hΓ, printedRate, hμ]
  simp only [diagMin, diagMax, Finset.inf'_const, Finset.sup'_const, Fin.sum_univ_two,
    Fintype.card_fin]
  norm_num [zMDP]
  positivity

/-- `A = diag(μ)(I − γP_π) = [[3/8, −1/8], [−1/8, 3/8]]`. -/
theorem zA_apply (s s' : Fin 2) :
    tdA zMDP zPolicy zMu s s' = if s = s' then 3 / 8 else -1 / 8 := by
  simp only [tdA, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    policyMatrix, Matrix.of_apply, zPolicyTransition_prob, zMu, uniformRow_two_prob,
    smul_eq_mul]
  fin_cases s <;> fin_cases s' <;> norm_num [zMDP]

/-- `det A = 1/8 ≠ 0`. -/
theorem zA_det_isUnit : IsUnit (tdA zMDP zPolicy zMu).det := by
  rw [Matrix.det_fin_two, zA_apply, zA_apply, zA_apply, zA_apply]
  norm_num

/-- A positive-weight sample has `s' = a`. -/
theorem next_eq_of_tupleProb_ne_zero {x : Tuple (Fin 2) (Fin 2)}
    (hx : tupleProb zMDP zPolicy zMu x ≠ 0) : x.2.2 = x.2.1 := by
  by_contra h
  apply hx
  simp only [tupleProb, zTransition_prob, if_neg h, mul_zero]

/-- On a positive-weight sample, a TD step at any step size fixes `V^π`. -/
theorem tdStep_zV {x : Tuple (Fin 2) (Fin 2)} (hx : tupleProb zMDP zPolicy zMu x ≠ 0)
    (η : ℝ) : tdStep zMDP η zV x = zV := by
  have hval : (1 - η) * zV x.1 + η * (zMDP.reward x.1 x.2.1 + zMDP.discount * zV x.2.2) =
      zV x.1 := by
    rw [next_eq_of_tupleProb_ne_zero hx, zReward_bellman]; ring
  rw [tdStep, hval, Function.update_eq_self]

/-- From `V₀ = V^π`, every positive-weight sample path leaves the iterates at `V^π`. -/
theorem tdIter_zV (η₀ : ℝ) {T : ℕ} {ω : Fin T → Tuple (Fin 2) (Fin 2)}
    (hω : pathWeight zMDP zPolicy zMu ω ≠ 0) (t : ℕ) : tdIter zMDP η₀ zV ω t = zV := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [tdIter]
    split_ifs with h
    · rw [ih]
      exact tdStep_zV (Finset.prod_ne_zero_iff.mp hω _ (Finset.mem_univ _)) _
    · exact ih

theorem scaledError_zero (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) {ω : Fin T → Tuple (Fin 2) (Fin 2)}
    (hω : pathWeight zMDP zPolicy zMu ω ≠ 0) :
    scaledError zMDP zPolicy η₀ (zMDP.valueFixedPoint zPolicy) ω = 0 := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hT)
  rw [scaledError, zValueFixedPoint, prAverage]
  simp only [tdIter_zV η₀ hω, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hT', one_smul, sub_self, smul_zero]

/-- The data law puts mass one on `{0}`: `P(√T Δ̄_T = 0) = 1`. -/
theorem lawProb_zero (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    lawProb zMDP zPolicy zMu η₀ (zMDP.valueFixedPoint zPolicy) T {0} = 1 := by
  rw [← sum_pathWeight zMDP zPolicy zMu T, lawProb]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  by_cases hω : pathWeight zMDP zPolicy zMu ω = 0
  · rw [hω, zero_mul]
  · rw [scaledError_zero η₀ hT hω, Set.indicator_of_mem (Set.mem_singleton 0), mul_one]

/-- Concrete witness: the convex distance is `1` at every `T ≥ 1`, attained at `{0}`. -/
theorem zeroNoise_dcvx_eq_one (η₀ : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    |lawProb zMDP zPolicy zMu η₀ (zMDP.valueFixedPoint zPolicy) T {0} -
      (gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)).real {0}| = 1 := by
  rw [lawProb_zero η₀ hT,
    gaussCov_real_singleton_zero _ _ zA_det_isUnit zPrintedGamma_pos]
  norm_num

end ZeroNoise

/-! ## The printed right-hand side tends to zero -/

/-- For any reals `a, b` some `T ≥ 1` has `a T^{-1/3} + b T^{-1/2} < 1`. -/
theorem exists_rhs_lt_one (a b : ℝ) :
    ∃ T : ℕ, 1 ≤ T ∧ a * (T : ℝ) ^ (-(1 / 3 : ℝ)) + b * (T : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
  set N : ℕ := ⌈|a| + |b|⌉₊ + 1 with hNdef
  have hN : |a| + |b| < (N : ℝ) := by
    rw [hNdef]; push_cast
    linarith [Nat.le_ceil (|a| + |b|)]
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈|a| + |b|⌉₊]
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨N ^ 6, Nat.one_le_pow _ _ (by exact_mod_cast hN0), ?_⟩
  have hpow : ∀ k : ℕ, ∀ e : ℝ, e * 6 = -(k : ℝ) →
      (((N ^ 6 : ℕ) : ℝ)) ^ e = ((N : ℝ) ^ k)⁻¹ := by
    intro k e he
    rw [Nat.cast_pow, ← Real.rpow_natCast (N : ℝ) 6, ← Real.rpow_mul hN0.le, mul_comm,
      Nat.cast_ofNat, he, Real.rpow_neg hN0.le, Real.rpow_natCast]
  rw [hpow 2 _ (by norm_num), hpow 3 _ (by norm_num)]
  have h2 : ((N : ℝ) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hN0 (by nlinarith)
  have h3 : ((N : ℝ) ^ 3)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hN0 (by nlinarith)
  have ha : a * ((N : ℝ) ^ 2)⁻¹ ≤ |a| * (N : ℝ)⁻¹ :=
    (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg a))
  have hb : b * ((N : ℝ) ^ 3)⁻¹ ≤ |b| * (N : ℝ)⁻¹ :=
    (mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg b))
  have hlt : (|a| + |b|) * (N : ℝ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hN0]; exact hN
  linarith

open ZeroNoise in
/-- Instance-level refutation core (check fix F3): for instance Z with `V₀ = V^π`, any step
parameter `η₀`, and *any* constants `c, C̃` (even chosen after the instance), some `T ≥ 1`
violates the printed bound on the closed convex set `{0}`. -/
theorem zeroNoise_violates (η₀ c Ct : ℝ) : ∃ T : ℕ, 1 ≤ T ∧
    c * printedRate zMDP zMu (printedGamma zMDP zPolicy zMu) η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
        Ct * (T : ℝ) ^ (-(1 / 2 : ℝ)) <
      |lawProb zMDP zPolicy zMu η₀ (zMDP.valueFixedPoint zPolicy) T {0} -
        (gaussCov (tdA zMDP zPolicy zMu) (printedGamma zMDP zPolicy zMu)).real {0}| := by
  obtain ⟨T, hT, hlt⟩ :=
    exists_rhs_lt_one (c * printedRate zMDP zMu (printedGamma zMDP zPolicy zMu) η₀) Ct
  exact ⟨T, hT, by rw [zeroNoise_dcvx_eq_one η₀ hT]; exact hlt⟩

open ZeroNoise in
/-- **Theorem 7.11 is false under the every-`V₀`, `r(s) = r_π(s)` reading**
(`thm:Berry-Esseen-linear`, `inference.tex:132–141`; SOURCE-ISSUES C43; action-dependent rewards
as printed), already on closed convex sets, at the zero-noise instance Z with `V₀ = V^π`,
`η₀ = 1/8`. -/
theorem not_thm7_11_printed : ¬ Thm7_11_printed := by
  rintro ⟨c, -, h⟩
  obtain ⟨Ct, -, hT⟩ := h (Fin 2) (Fin 2) zMDP zPolicy zMu (1 / 8)
    (zMDP.valueFixedPoint zPolicy) zMu_pos (by norm_num) (by norm_num) zPrintedGamma_pos
  obtain ⟨T, hT1, hlt⟩ := zeroNoise_violates (1 / 8) c Ct
  exact absurd (hT T hT1 {0} (convex_singleton 0) isClosed_singleton) (not_le.2 hlt)

open ZeroNoise in
/-- The instance-wise reading (constants `c, C̃` chosen per instance) is also false (F3). -/
theorem not_thm7_11_printed_instWise : ¬ Thm7_11_printed_instWise := by
  intro h
  obtain ⟨c, -, Ct, -, hT⟩ := h (Fin 2) (Fin 2) zMDP zPolicy zMu (1 / 8)
    (zMDP.valueFixedPoint zPolicy) zMu_pos (by norm_num) (by norm_num) zPrintedGamma_pos
  obtain ⟨T, hT1, hlt⟩ := zeroNoise_violates (1 / 8) c Ct
  exact absurd (hT T hT1 {0} (convex_singleton 0) isClosed_singleton) (not_le.2 hlt)

/-- The literal all-convex-sets reading is false too. -/
theorem not_thm7_11_printed_allConvex : ¬ Thm7_11_printed_allConvex :=
  fun h ↦ not_thm7_11_printed (thm7_11_printed_allConvex_imp h)

end StatisticalRL.Ch7Rest.TDInference
