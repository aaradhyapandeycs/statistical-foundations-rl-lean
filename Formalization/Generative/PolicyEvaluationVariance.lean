import Formalization.MDP.PrefixValueBridge
import Formalization.Probability.Variance
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Variance self-bounding for true policy trajectories

A pointwise Bellman/variance identity yields a nonnegative potential that
bounds every finite discounted sum of true policy-transition variances.
This is an intermediate toward, not a proof of, the source's resolvent bound.
-/

open Filter
open scoped Topology

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The known one-step policy-averaged reward. -/
def evaluationPolicyReward (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  (π s).expectation (M.reward s)

/-- Population variance of the actual true trajectory value under the policy row. -/
noncomputable def evaluationPolicyVariance (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  (M.policyTransition π s).variance (M.trajectoryExpectedValue π)

/-- The Bellman relation for actual infinite-trajectory value. -/
theorem evaluationTrajectory_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.trajectoryExpectedValue π s = evaluationPolicyReward M π s +
      M.discount * (M.policyTransition π s).expectation (M.trajectoryExpectedValue π) := by
  have h := congrFun (M.valueFixedPoint_spec π) s
  rw [← M.trajectoryExpectedValue_eq_valueFixedPoint π] at h
  exact h.symm

/-- Exact second-moment identity, with no division by the discount. -/
theorem evaluationPolicyVariance_identity (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.discount ^ 2 * evaluationPolicyVariance M π s =
      M.discount ^ 2 * (M.policyTransition π s).expectation
        (fun t ↦ (M.trajectoryExpectedValue π t) ^ 2) -
      (M.trajectoryExpectedValue π s) ^ 2 +
      2 * M.trajectoryExpectedValue π s * evaluationPolicyReward M π s -
      (evaluationPolicyReward M π s) ^ 2 := by
  have hb := evaluationTrajectory_bellman M π s
  have hsq : (M.trajectoryExpectedValue π s - evaluationPolicyReward M π s) ^ 2 =
      M.discount ^ 2 * ((M.policyTransition π s).expectation (M.trajectoryExpectedValue π)) ^ 2 := by
    rw [hb]
    ring
  unfold evaluationPolicyVariance FiniteDistribution.variance
  nlinarith only [hsq]

/-- The pointwise inequality used in the source variance argument, multiplied
by γ² so it also holds at γ=0. -/
theorem evaluationPolicyVariance_selfBound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.discount ^ 2 * evaluationPolicyVariance M π s ≤
      M.discount * (M.policyTransition π s).expectation
        (fun t ↦ (M.trajectoryExpectedValue π t) ^ 2) -
      (M.trajectoryExpectedValue π s) ^ 2 +
      2 * M.trajectoryExpectedValue π s * evaluationPolicyReward M π s := by
  have hγ : M.discount ^ 2 ≤ M.discount := by
    nlinarith [M.discount_nonneg, M.discount_lt_one]
  have hE : 0 ≤ (M.policyTransition π s).expectation
      (fun t ↦ (M.trajectoryExpectedValue π t) ^ 2) :=
    (M.policyTransition π s).expectation_nonneg (fun _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hγ hE
  have hid := evaluationPolicyVariance_identity M π s
  have hsq := sq_nonneg (evaluationPolicyReward M π s)
  nlinarith only [hmul, hid, hsq]

/-- Nonnegative Lyapunov potential for the discounted variance recursion. -/
noncomputable def evaluationVariancePotential (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  2 * ‖M.trajectoryExpectedValue π‖ * M.trajectoryExpectedValue π s -
    (M.trajectoryExpectedValue π s) ^ 2

theorem evaluationVariancePotential_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ evaluationVariancePotential M π s ∧
      evaluationVariancePotential M π s ≤ ‖M.trajectoryExpectedValue π‖ ^ 2 := by
  have hv : 0 ≤ M.trajectoryExpectedValue π s := (M.trajectoryExpectedValue_bounds π s).1
  have hle : M.trajectoryExpectedValue π s ≤ ‖M.trajectoryExpectedValue π‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hv] using
      norm_le_pi_norm (M.trajectoryExpectedValue π) s
  have hs := sq_nonneg (‖M.trajectoryExpectedValue π‖ - M.trajectoryExpectedValue π s)
  unfold evaluationVariancePotential
  constructor <;> nlinarith

/-- The potential dominates one variance step plus its discounted future. -/
theorem evaluationVariancePotential_super (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.discount ^ 2 * evaluationPolicyVariance M π s +
      M.discount * (M.policyTransition π s).expectation (evaluationVariancePotential M π) ≤
        evaluationVariancePotential M π s := by
  let V := M.trajectoryExpectedValue π
  let B := ‖V‖
  let r := evaluationPolicyReward M π s
  have hr : 0 ≤ r := (π s).expectation_nonneg (M.reward_nonneg s)
  have hv : 0 ≤ V s := (M.trajectoryExpectedValue_bounds π s).1
  have hVB : V s ≤ B := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hv] using norm_le_pi_norm V s
  have hprod : 0 ≤ (B - V s) * r := mul_nonneg (sub_nonneg.mpr hVB) hr
  have hb : V s = r + M.discount * (M.policyTransition π s).expectation V :=
    evaluationTrajectory_bellman M π s
  have hbB : 2 * B * V s = 2 * B * r +
      2 * B * M.discount * (M.policyTransition π s).expectation V := by
    rw [hb]
    ring
  have hP : (M.policyTransition π s).expectation (evaluationVariancePotential M π) =
      2 * B * (M.policyTransition π s).expectation V -
        (M.policyTransition π s).expectation (fun t ↦ V t ^ 2) := by
    change (M.policyTransition π s).expectation (fun t ↦ 2 * B * V t - V t ^ 2) = _
    rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_mul]
  have hvar := evaluationPolicyVariance_selfBound M π s
  change M.discount ^ 2 * evaluationPolicyVariance M π s ≤
      M.discount * (M.policyTransition π s).expectation (fun t ↦ V t ^ 2) -
        V s ^ 2 + 2 * V s * r at hvar
  rw [hP]
  change M.discount ^ 2 * evaluationPolicyVariance M π s +
      M.discount * (2 * B * (M.policyTransition π s).expectation V -
        (M.policyTransition π s).expectation (fun t ↦ V t ^ 2)) ≤
          2 * B * V s - V s ^ 2
  nlinarith only [hvar, hbB, hprod]

/-- The first n terms of the discounted policy-variance recursion, scaled by γ². -/
noncomputable def discountedPolicyVariancePartial (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : ℕ → State → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 => fun s ↦ M.discount ^ 2 * evaluationPolicyVariance M π s +
      M.discount * (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n)

/-- Every finite partial sum is nonnegative and bounded by the true-value potential. -/
theorem discountedPolicyVariancePartial_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    0 ≤ discountedPolicyVariancePartial M π n s ∧
      discountedPolicyVariancePartial M π n s ≤ evaluationVariancePotential M π s := by
  induction n generalizing s with
  | zero =>
      exact ⟨le_rfl, (evaluationVariancePotential_bounds M π s).1⟩
  | succ n ih =>
      have hnon : 0 ≤ (M.policyTransition π s).expectation
          (discountedPolicyVariancePartial M π n) :=
        (M.policyTransition π s).expectation_nonneg (fun t ↦ (ih t).1)
      have hmono : (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n) ≤
          (M.policyTransition π s).expectation (evaluationVariancePotential M π) :=
        (M.policyTransition π s).expectation_mono (fun t ↦ (ih t).2)
      constructor
      · exact add_nonneg (mul_nonneg (sq_nonneg _) ((M.policyTransition π s).variance_nonneg _))
          (mul_nonneg M.discount_nonneg hnon)
      · calc
          _ ≤ M.discount ^ 2 * evaluationPolicyVariance M π s +
              M.discount * (M.policyTransition π s).expectation (evaluationVariancePotential M π) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hmono M.discount_nonneg)
          _ ≤ _ := evaluationVariancePotential_super M π s

/-- Uniform finite-horizon variance budget. -/
theorem discountedPolicyVariancePartial_le_norm_sq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) :
    discountedPolicyVariancePartial M π n s ≤ ‖M.trajectoryExpectedValue π‖ ^ 2 :=
  (discountedPolicyVariancePartial_bounds M π n s).2.trans
    (evaluationVariancePotential_bounds M π s).2


/-- The finite discounted variance budgets increase with the horizon. -/
theorem discountedPolicyVariancePartial_mono (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Monotone (fun n ↦ discountedPolicyVariancePartial M π n s) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing s with
  | zero =>
      exact (discountedPolicyVariancePartial_bounds M π 1 s).1
  | succ n ih =>
      change M.discount ^ 2 * evaluationPolicyVariance M π s +
          M.discount * (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n) ≤
        M.discount ^ 2 * evaluationPolicyVariance M π s +
          M.discount * (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π (n + 1))
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ M.discount_nonneg
      exact (M.policyTransition π s).expectation_mono (fun t ↦ ih t)

/-- The infinite budget is the supremum of the actual finite recursions. -/
noncomputable def discountedPolicyVarianceBudget (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  ⨆ n, discountedPolicyVariancePartial M π n s

/-- The finite budgets converge to the bounded infinite budget. -/
theorem discountedPolicyVariancePartial_tendsto (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Tendsto (fun n ↦ discountedPolicyVariancePartial M π n s) atTop
      (𝓝 (discountedPolicyVarianceBudget M π s)) := by
  apply tendsto_atTop_ciSup (discountedPolicyVariancePartial_mono M π s)
  exact ⟨‖M.trajectoryExpectedValue π‖ ^ 2, by
    rintro _ ⟨n, rfl⟩
    exact discountedPolicyVariancePartial_le_norm_sq M π n s⟩

/-- The infinite discounted variance budget retains the same sharp potential bound. -/
theorem discountedPolicyVarianceBudget_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ discountedPolicyVarianceBudget M π s ∧
      discountedPolicyVarianceBudget M π s ≤ evaluationVariancePotential M π s := by
  have ht := discountedPolicyVariancePartial_tendsto M π s
  exact ⟨ge_of_tendsto' ht (fun n ↦ (discountedPolicyVariancePartial_bounds M π n s).1),
    le_of_tendsto' ht (fun n ↦ (discountedPolicyVariancePartial_bounds M π n s).2)⟩

/-- The infinite budget solves the true-policy discounted variance equation. -/
theorem discountedPolicyVarianceBudget_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    discountedPolicyVarianceBudget M π s =
      M.discount ^ 2 * evaluationPolicyVariance M π s +
        M.discount * (M.policyTransition π s).expectation (discountedPolicyVarianceBudget M π) := by
  have hleft := (discountedPolicyVariancePartial_tendsto M π s).comp (tendsto_add_atTop_nat 1)
  have hE : Tendsto (fun n ↦ (M.policyTransition π s).expectation
      (discountedPolicyVariancePartial M π n)) atTop
      (𝓝 ((M.policyTransition π s).expectation (discountedPolicyVarianceBudget M π))) := by
    unfold FiniteDistribution.expectation
    apply tendsto_finset_sum
    intro t _
    exact tendsto_const_nhds.mul (discountedPolicyVariancePartial_tendsto M π t)
  have hright : Tendsto (fun n : ℕ ↦ M.discount ^ 2 * evaluationPolicyVariance M π s +
      M.discount * (M.policyTransition π s).expectation (discountedPolicyVariancePartial M π n)) atTop
      (𝓝 (M.discount ^ 2 * evaluationPolicyVariance M π s +
        M.discount * (M.policyTransition π s).expectation (discountedPolicyVarianceBudget M π))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hE)
  change Tendsto (fun n ↦ discountedPolicyVariancePartial M π (n + 1) s) atTop
    (𝓝 (M.discount ^ 2 * evaluationPolicyVariance M π s +
      M.discount * (M.policyTransition π s).expectation (discountedPolicyVarianceBudget M π))) at hright
  exact tendsto_nhds_unique hleft hright

/-- The resulting infinite variance budget is at most the squared true-value sup norm. -/
theorem discountedPolicyVarianceBudget_le_norm_sq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    discountedPolicyVarianceBudget M π s ≤ ‖M.trajectoryExpectedValue π‖ ^ 2 :=
  (discountedPolicyVarianceBudget_bounds M π s).2.trans
    (evaluationVariancePotential_bounds M π s).2


/-- The discounted variance equation has no other real-valued solution. -/
theorem discountedPolicyVarianceBudget_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (W : State → ℝ)
    (hW : ∀ s, W s = M.discount ^ 2 * evaluationPolicyVariance M π s +
      M.discount * (M.policyTransition π s).expectation W) :
    W = discountedPolicyVarianceBudget M π := by
  let B := discountedPolicyVarianceBudget M π
  have hdiff : W - B = M.valueBellman π W - M.valueBellman π B := by
    funext s
    have hb := discountedPolicyVarianceBudget_bellman M π s
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

end StatisticalRL.DiscountedMDP
