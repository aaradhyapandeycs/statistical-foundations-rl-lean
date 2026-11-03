import Formalization.Generative.PolicyEvaluationVariance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Finite square-root policy-variance budgets for a discounted MDP. -/

open Filter
open scoped Topology BigOperators Matrix

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Finite-distribution Jensen inequality for a square. -/
theorem evaluation_expectation_sq_le (d : FiniteDistribution State) (f : State → ℝ) :
    (d.expectation f) ^ 2 ≤ d.expectation (fun t ↦ f t ^ 2) := by
  have h := d.variance_nonneg f
  unfold FiniteDistribution.variance at h
  linarith

/-- Finite discounted square-root variance recursion, scaled by γ. -/
noncomputable def discountedPolicySqrtVariancePartial (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : ℕ → State → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 => fun s ↦ M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
      M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVariancePartial M π n)

/-- Finite-horizon Jensen bound connecting the square-root recursion to the
already constructed scaled variance budget. -/
theorem discountedPolicySqrtVariancePartial_sq_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    0 ≤ discountedPolicySqrtVariancePartial M π n s ∧
      (1 - M.discount) * (discountedPolicySqrtVariancePartial M π n s) ^ 2 ≤
        discountedPolicyVariancePartial M π n s := by
  induction n generalizing s with
  | zero => simp [discountedPolicySqrtVariancePartial, discountedPolicyVariancePartial]
  | succ n ih =>
      let d : ℝ := 1 - M.discount
      let A : ℝ := M.discount * Real.sqrt (evaluationPolicyVariance M π s)
      let B : ℝ := (M.policyTransition π s).expectation (discountedPolicySqrtVariancePartial M π n)
      have hd : 0 ≤ d := (sub_pos.mpr M.discount_lt_one).le
      have hvar : 0 ≤ evaluationPolicyVariance M π s :=
        (M.policyTransition π s).variance_nonneg _
      have hnon : 0 ≤ B :=
        (M.policyTransition π s).expectation_nonneg (fun t ↦ (ih t).1)
      have hA : A ^ 2 = M.discount ^ 2 * evaluationPolicyVariance M π s := by
        dsimp [A]
        rw [mul_pow, Real.sq_sqrt hvar]
      have hJ : B ^ 2 ≤ (M.policyTransition π s).expectation
          (fun t ↦ (discountedPolicySqrtVariancePartial M π n t) ^ 2) :=
        evaluation_expectation_sq_le _ _
      have hI : (M.policyTransition π s).expectation
          (fun t ↦ d * (discountedPolicySqrtVariancePartial M π n t) ^ 2) ≤
          (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n) :=
        (M.policyTransition π s).expectation_mono (fun t ↦ (ih t).2)
      rw [FiniteDistribution.expectation_mul] at hI
      have hB : d * B ^ 2 ≤ (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n) :=
        (mul_le_mul_of_nonneg_left hJ hd).trans hI
      have hscalar : d * (A + M.discount * B) ^ 2 ≤
          A ^ 2 + M.discount * d * B ^ 2 := by
        have hid : A ^ 2 + M.discount * d * B ^ 2 - d * (A + M.discount * B) ^ 2 =
            M.discount * (A - d * B) ^ 2 := by dsimp [d]; ring
        have hp := mul_nonneg M.discount_nonneg (sq_nonneg (A - d * B))
        linarith
      constructor
      · change 0 ≤ A + M.discount * B
        exact add_nonneg (mul_nonneg M.discount_nonneg (Real.sqrt_nonneg _))
          (mul_nonneg M.discount_nonneg hnon)
      · change d * (A + M.discount * B) ^ 2 ≤
          M.discount ^ 2 * evaluationPolicyVariance M π s +
            M.discount * (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n)
        have hmul := mul_le_mul_of_nonneg_left hB M.discount_nonneg
        rw [← hA]
        nlinarith only [hscalar, hmul]

/-- The square-root recursion is bounded by the true trajectory value norm. -/
theorem discountedPolicySqrtVariancePartial_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    discountedPolicySqrtVariancePartial M π n s ≤
      ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) := by
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hs : 0 < Real.sqrt (1 - M.discount) := Real.sqrt_pos.2 hd
  have hs2 := Real.sq_sqrt hd.le
  have hR := discountedPolicySqrtVariancePartial_sq_le M π n s
  have hB := discountedPolicyVariancePartial_le_norm_sq M π n s
  have hn : 0 ≤ ‖M.trajectoryExpectedValue π‖ := norm_nonneg _
  apply (le_div_iff₀ hs).2
  have hsqr : (discountedPolicySqrtVariancePartial M π n s * Real.sqrt (1 - M.discount)) ^ 2 ≤
      ‖M.trajectoryExpectedValue π‖ ^ 2 := by
    rw [mul_pow, hs2]
    nlinarith only [hR.2, hB]
  exact (sq_le_sq₀ (mul_nonneg hR.1 hs.le) hn).mp hsqr


/-- The finite square-root variance recursions are monotone. -/
theorem discountedPolicySqrtVariancePartial_mono (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Monotone (fun n ↦ discountedPolicySqrtVariancePartial M π n s) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing s with
  | zero => exact (discountedPolicySqrtVariancePartial_sq_le M π 1 s).1
  | succ n ih =>
      change M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
          M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVariancePartial M π n) ≤
        M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
          M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVariancePartial M π (n + 1))
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((M.policyTransition π s).expectation_mono (fun t ↦ ih t)) M.discount_nonneg)

/-- Infinite γ-scaled square-root variance budget as a monotone finite-horizon limit. -/
noncomputable def discountedPolicySqrtVarianceBudget (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  ⨆ n, discountedPolicySqrtVariancePartial M π n s

/-- The square-root budgets converge. -/
theorem discountedPolicySqrtVariancePartial_tendsto (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Tendsto (fun n ↦ discountedPolicySqrtVariancePartial M π n s) atTop
      (𝓝 (discountedPolicySqrtVarianceBudget M π s)) := by
  apply tendsto_atTop_ciSup (discountedPolicySqrtVariancePartial_mono M π s)
  exact ⟨‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount), by
    rintro _ ⟨n, rfl⟩
    exact discountedPolicySqrtVariancePartial_bound M π n s⟩

/-- The limiting scaled square-root budget is bounded at every state. -/
theorem discountedPolicySqrtVarianceBudget_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ discountedPolicySqrtVarianceBudget M π s ∧
      discountedPolicySqrtVarianceBudget M π s ≤
        ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) := by
  have ht := discountedPolicySqrtVariancePartial_tendsto M π s
  exact ⟨ge_of_tendsto' ht (fun n ↦ (discountedPolicySqrtVariancePartial_sq_le M π n s).1),
    le_of_tendsto' ht (fun n ↦ discountedPolicySqrtVariancePartial_bound M π n s)⟩


/-- The entire scaled square-root budget obeys the source-relevant sup-norm bound. -/
theorem discountedPolicySqrtVarianceBudget_norm_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ‖discountedPolicySqrtVarianceBudget M π‖ ≤
      ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) := by
  have hc : 0 ≤ ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) :=
    div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  have h := discountedPolicySqrtVarianceBudget_bounds M π s
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- The limiting square-root budget satisfies the true-policy discounted equation. -/
theorem discountedPolicySqrtVarianceBudget_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    discountedPolicySqrtVarianceBudget M π s =
      M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
        M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVarianceBudget M π) := by
  have hleft := (discountedPolicySqrtVariancePartial_tendsto M π s).comp (tendsto_add_atTop_nat 1)
  have hE : Tendsto (fun n ↦ (M.policyTransition π s).expectation
      (discountedPolicySqrtVariancePartial M π n)) atTop
      (𝓝 ((M.policyTransition π s).expectation (discountedPolicySqrtVarianceBudget M π))) := by
    unfold FiniteDistribution.expectation
    apply tendsto_finset_sum
    intro t _
    exact tendsto_const_nhds.mul (discountedPolicySqrtVariancePartial_tendsto M π t)
  have hright : Tendsto (fun n : ℕ ↦ M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
      M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVariancePartial M π n)) atTop
      (𝓝 (M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
        M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVarianceBudget M π))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hE)
  change Tendsto (fun n ↦ discountedPolicySqrtVariancePartial M π (n + 1) s) atTop
    (𝓝 (M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
      M.discount * (M.policyTransition π s).expectation (discountedPolicySqrtVarianceBudget M π))) at hright
  exact tendsto_nhds_unique hleft hright

/-- The limit inherits Jensen's direct comparison with the variance budget. -/
theorem discountedPolicySqrtVarianceBudget_sq_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    (1 - M.discount) * (discountedPolicySqrtVarianceBudget M π s) ^ 2 ≤
      discountedPolicyVarianceBudget M π s := by
  have hR := discountedPolicySqrtVariancePartial_tendsto M π s
  have hV := discountedPolicyVariancePartial_tendsto M π s
  have hleft : Tendsto (fun n ↦ (1 - M.discount) * (discountedPolicySqrtVariancePartial M π n s) ^ 2)
      atTop (𝓝 ((1 - M.discount) * (discountedPolicySqrtVarianceBudget M π s) ^ 2)) :=
    tendsto_const_nhds.mul (hR.pow 2)
  exact le_of_tendsto_of_tendsto' hleft hV
    (fun n ↦ (discountedPolicySqrtVariancePartial_sq_le M π n s).2)

/-- The scaled square-root variance equation has a unique solution. -/
theorem discountedPolicySqrtVarianceBudget_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (W : State → ℝ)
    (hW : ∀ s, W s = M.discount * Real.sqrt (evaluationPolicyVariance M π s) +
      M.discount * (M.policyTransition π s).expectation W) :
    W = discountedPolicySqrtVarianceBudget M π := by
  let B := discountedPolicySqrtVarianceBudget M π
  have hdiff : W - B = M.valueBellman π W - M.valueBellman π B := by
    funext s
    have hb := discountedPolicySqrtVarianceBudget_bellman M π s
    have hs := hW s
    change W s - B s = M.valueBellman π W s - M.valueBellman π B s
    simp only [valueBellman]
    dsimp [B] at hs ⊢
    nlinarith only [hs, hb]
  have hnorm : ‖W - B‖ ≤ M.discount * ‖W - B‖ := by
    calc
      ‖W - B‖ = ‖M.valueBellman π W - M.valueBellman π B‖ := congrArg norm hdiff
      _ ≤ _ := M.norm_valueBellman_sub_le π W B
  have hzero : ‖W - B‖ = 0 := by
    have hn := norm_nonneg (W - B)
    have hg := M.discount_lt_one
    nlinarith only [hn, hg, hnorm]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)


/-- The t-fold true policy kernel applied to a state vector. -/
noncomputable def evaluationPolicyKernelIter (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) : ℕ → State → ℝ
  | 0 => f
  | n + 1 => fun s ↦ (M.policyTransition π s).expectation (evaluationPolicyKernelIter M π f n)

/-- Generic finite discounted kernel recursion. -/
noncomputable def evaluationDiscountedKernelPartial (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) : ℕ → State → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 => fun s ↦ f s + M.discount *
      (M.policyTransition π s).expectation (evaluationDiscountedKernelPartial M π f n)

/-- Finite transition expectation commutes with a finite sum. -/
theorem evaluation_expectation_finset_sum {ι : Type*} (d : FiniteDistribution State)
    (I : Finset ι) (f : ι → State → ℝ) :
    d.expectation (fun s ↦ ∑ i ∈ I, f i s) = ∑ i ∈ I, d.expectation (f i) := by
  classical
  unfold FiniteDistribution.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The finite recursion is exactly the corresponding discounted kernel sum. -/
theorem evaluationDiscountedKernelPartial_expansion (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (n : ℕ) (s : State) :
    evaluationDiscountedKernelPartial M π f n s =
      ∑ i ∈ Finset.range n, M.discount ^ i * evaluationPolicyKernelIter M π f i s := by
  induction n generalizing s with
  | zero => simp [evaluationDiscountedKernelPartial]
  | succ n ih =>
      rw [evaluationDiscountedKernelPartial, Finset.sum_range_succ']
      simp only [pow_zero, one_mul, evaluationPolicyKernelIter]
      have heq : evaluationDiscountedKernelPartial M π f n =
          (fun t ↦ ∑ i ∈ Finset.range n, M.discount ^ i * evaluationPolicyKernelIter M π f i t) := by
        funext t
        exact ih t
      rw [heq, evaluation_expectation_finset_sum]
      simp_rw [FiniteDistribution.expectation_mul, Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [pow_succ]
      ring

/-- The scaled true variance recursion is the generic discounted kernel recursion. -/
theorem discountedPolicyVariancePartial_eq_kernelPartial (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    discountedPolicyVariancePartial M π n =
      evaluationDiscountedKernelPartial M π (fun s ↦ M.discount ^ 2 * evaluationPolicyVariance M π s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext s
      simp only [discountedPolicyVariancePartial, evaluationDiscountedKernelPartial, ih]

/-- The square-root recursion is the generic discounted kernel recursion. -/
theorem discountedPolicySqrtVariancePartial_eq_kernelPartial (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    discountedPolicySqrtVariancePartial M π n =
      evaluationDiscountedKernelPartial M π (fun s ↦ M.discount * Real.sqrt (evaluationPolicyVariance M π s)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext s
      simp only [discountedPolicySqrtVariancePartial, evaluationDiscountedKernelPartial, ih]

/-- Explicit finite-sum expansion of the scaled variance partial budget. -/
theorem discountedPolicyVariancePartial_expansion (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    discountedPolicyVariancePartial M π n s =
      ∑ i ∈ Finset.range n, M.discount ^ i * evaluationPolicyKernelIter M π
        (fun t ↦ M.discount ^ 2 * evaluationPolicyVariance M π t) i s := by
  rw [discountedPolicyVariancePartial_eq_kernelPartial, evaluationDiscountedKernelPartial_expansion]

/-- Explicit finite-sum expansion of the scaled square-root partial budget. -/
theorem discountedPolicySqrtVariancePartial_expansion (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    discountedPolicySqrtVariancePartial M π n s =
      ∑ i ∈ Finset.range n, M.discount ^ i * evaluationPolicyKernelIter M π
        (fun t ↦ M.discount * Real.sqrt (evaluationPolicyVariance M π t)) i s := by
  rw [discountedPolicySqrtVariancePartial_eq_kernelPartial, evaluationDiscountedKernelPartial_expansion]


noncomputable local instance varianceResolventStateDecidable : DecidableEq State := Classical.decEq State

/-- The true policy transition kernel as a finite matrix. -/
noncomputable def evaluationPolicyMatrix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : Matrix State State ℝ :=
  fun s t ↦ (M.policyTransition π s).prob t

theorem evaluationPolicyMatrix_mulVec (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) (s : State) :
    (evaluationPolicyMatrix M π *ᵥ V) s = (M.policyTransition π s).expectation V := rfl

/-- The true-policy discounted matrix resolvent is invertible. -/
theorem evaluationPolicyResolvent_isUnit (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    IsUnit (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hnorm : ‖x - y‖ ≤ M.discount * ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount_nonneg (norm_nonneg _))).2
    intro s
    have hs := congrFun hxy s
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [evaluationPolicyMatrix_mulVec, evaluationPolicyMatrix_mulVec] at hs
    have hrow := (M.policyTransition π s).abs_expectation_sub_le
      (f := x) (g := y) (c := ‖x - y‖) (fun t ↦ by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) t)
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have heq : x s - y s = M.discount *
        ((M.policyTransition π s).expectation x - (M.policyTransition π s).expectation y) := by linarith
    rw [heq, abs_mul, abs_of_nonneg M.discount_nonneg]
    exact mul_le_mul_of_nonneg_left hrow M.discount_nonneg
  have hz : ‖x - y‖ = 0 := by
    by_contra hn
    have hp : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hlt := M.discount_lt_one
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The infinite scaled square-root budget is the literal matrix resolvent. -/
theorem discountedPolicySqrtVarianceBudget_eq_inverse (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (fun s ↦ M.discount * Real.sqrt (evaluationPolicyVariance M π s)) =
        discountedPolicySqrtVarianceBudget M π := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  apply Matrix.inv_mulVec_eq_vec
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec]
  have hb := discountedPolicySqrtVarianceBudget_bellman M π s
  linarith

/-- The source-relevant true resolvent square-root variance bound, scaled by γ.
It is valid at γ=0 without dividing by the discount. -/
theorem evaluationPolicyResolvent_sqrtVariance_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    M.discount * ‖(1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (fun s ↦ Real.sqrt (evaluationPolicyVariance M π s))‖ ≤
        ‖M.trajectoryExpectedValue π‖ / Real.sqrt (1 - M.discount) := by
  have heq := discountedPolicySqrtVarianceBudget_eq_inverse M π
  change (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (M.discount • (fun s ↦ Real.sqrt (evaluationPolicyVariance M π s))) = _ at heq
  rw [Matrix.mulVec_smul] at heq
  have hn := congrArg norm heq
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg M.discount_nonneg] at hn
  rw [hn]
  exact discountedPolicySqrtVarianceBudget_norm_bound M π


/-- The infinite scaled variance budget is the literal true matrix resolvent. -/
theorem discountedPolicyVarianceBudget_eq_inverse (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (fun s ↦ M.discount ^ 2 * evaluationPolicyVariance M π s) =
        discountedPolicyVarianceBudget M π := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  apply Matrix.inv_mulVec_eq_vec
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec]
  have hb := discountedPolicyVarianceBudget_bellman M π s
  linarith

/-- Pointwise identification of the scaled variance resolvent. -/
theorem evaluationPolicyResolvent_variance_scaled (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.discount ^ 2 * ((1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      evaluationPolicyVariance M π) s = discountedPolicyVarianceBudget M π s := by
  have heq := discountedPolicyVarianceBudget_eq_inverse M π
  change (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (M.discount ^ 2 • evaluationPolicyVariance M π) = _ at heq
  rw [Matrix.mulVec_smul] at heq
  exact congrFun heq s

/-- Pointwise identification of the scaled square-root variance resolvent. -/
theorem evaluationPolicyResolvent_sqrtVariance_scaled (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.discount * ((1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (fun t ↦ Real.sqrt (evaluationPolicyVariance M π t))) s =
        discountedPolicySqrtVarianceBudget M π s := by
  have heq := discountedPolicySqrtVarianceBudget_eq_inverse M π
  change (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (M.discount • (fun t ↦ Real.sqrt (evaluationPolicyVariance M π t))) = _ at heq
  rw [Matrix.mulVec_smul] at heq
  exact congrFun heq s

/-- Literal scaled true-resolvent Jensen inequality. -/
theorem evaluationPolicyResolvent_jensen (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    (1 - M.discount) * (M.discount *
      ((1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
        (fun t ↦ Real.sqrt (evaluationPolicyVariance M π t))) s) ^ 2 ≤
      M.discount ^ 2 * ((1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
        evaluationPolicyVariance M π) s := by
  rw [evaluationPolicyResolvent_sqrtVariance_scaled, evaluationPolicyResolvent_variance_scaled]
  exact discountedPolicySqrtVarianceBudget_sq_le M π s

/-- Literal scaled true-resolvent variance budget. -/
theorem evaluationPolicyResolvent_variance_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ M.discount ^ 2 * ((1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      evaluationPolicyVariance M π) s ∧
    M.discount ^ 2 * ((1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      evaluationPolicyVariance M π) s ≤ ‖M.trajectoryExpectedValue π‖ ^ 2 := by
  rw [evaluationPolicyResolvent_variance_scaled]
  exact ⟨(discountedPolicyVarianceBudget_bounds M π s).1,
    discountedPolicyVarianceBudget_le_norm_sq M π s⟩


/-- The t-fold policy kernel commutes with scalar multiplication. -/
theorem evaluationPolicyKernelIter_const_mul (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (c : ℝ) (f : State → ℝ) (n : ℕ) (s : State) :
    evaluationPolicyKernelIter M π (fun t ↦ c * f t) n s =
      c * evaluationPolicyKernelIter M π f n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change (M.policyTransition π s).expectation
          (evaluationPolicyKernelIter M π (fun t ↦ c * f t) n) =
        c * (M.policyTransition π s).expectation (evaluationPolicyKernelIter M π f n)
      have heq : evaluationPolicyKernelIter M π (fun t ↦ c * f t) n =
          (fun t ↦ c * evaluationPolicyKernelIter M π f n t) := by
        funext t
        exact ih t
      rw [heq, FiniteDistribution.expectation_mul]

/-- The variance budget has the literal finite discounted sum with γ^{t+2}. -/
theorem discountedPolicyVariancePartial_explicit (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    discountedPolicyVariancePartial M π n s =
      ∑ i ∈ Finset.range n, M.discount ^ (i + 2) *
        evaluationPolicyKernelIter M π (evaluationPolicyVariance M π) i s := by
  rw [discountedPolicyVariancePartial_expansion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evaluationPolicyKernelIter_const_mul, pow_add]
  ring

/-- The square-root budget has the literal finite discounted sum with γ^{t+1}. -/
theorem discountedPolicySqrtVariancePartial_explicit (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    discountedPolicySqrtVariancePartial M π n s =
      ∑ i ∈ Finset.range n, M.discount ^ (i + 1) *
        evaluationPolicyKernelIter M π (fun t ↦ Real.sqrt (evaluationPolicyVariance M π t)) i s := by
  rw [discountedPolicySqrtVariancePartial_expansion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evaluationPolicyKernelIter_const_mul, pow_succ]
  ring

/-- For positive discount, the unscaled literal resolvent has the source's
shape, with an improved constant one. -/
theorem evaluationPolicyResolvent_sqrtVariance_bound_of_pos (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hγ : 0 < M.discount) :
    ‖(1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (fun s ↦ Real.sqrt (evaluationPolicyVariance M π s))‖ ≤
        ‖M.trajectoryExpectedValue π‖ / (M.discount * Real.sqrt (1 - M.discount)) := by
  have hs : 0 < Real.sqrt (1 - M.discount) := Real.sqrt_pos.2 (sub_pos.mpr M.discount_lt_one)
  have h := evaluationPolicyResolvent_sqrtVariance_bound M π
  have hh := (le_div_iff₀ hs).mp h
  apply (le_div_iff₀ (mul_pos hγ hs)).2
  calc
    _ = M.discount * ‖(1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
        (fun s ↦ Real.sqrt (evaluationPolicyVariance M π s))‖ * Real.sqrt (1 - M.discount) := by ring
    _ ≤ _ := hh

end StatisticalRL.DiscountedMDP
