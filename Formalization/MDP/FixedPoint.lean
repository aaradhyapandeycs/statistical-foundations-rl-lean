import Formalization.MDP.FixedPointDefinitions

/-!
# Bellman fixed points and value iteration

Existence is proved before a fixed-point object is selected. These are the
unique fixed points of the actual Bellman operators from Chapter 2 of
arXiv:2610.41903v1. Their identification with expected trajectory returns and
with the trajectory-optimal Q-function is a separate semantic obligation.
-/

open Filter
open scoped Topology NNReal

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Complete defining equation for the selected policy Bellman solution. -/
theorem policyFixedPoint_spec (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    M.qBellman π (M.policyFixedPoint π) = M.policyFixedPoint π :=
  (Classical.choose_spec (M.policy_fixedPoint_exists_unique π)).1

/-- Complete defining equation for the selected optimality Bellman solution. -/
theorem optimalityFixedPoint_spec (M : DiscountedMDP State Action) :
    M.qOptimality M.optimalityFixedPoint = M.optimalityFixedPoint :=
  (Classical.choose_spec M.optimality_fixedPoint_exists_unique).1

theorem policyFixedPoint_characterization (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (Q : State → Action → ℝ) :
    M.qBellman π Q = Q ↔ Q = M.policyFixedPoint π := by
  constructor
  · intro hQ
    exact M.qBellman_fixedpoint_unique π hQ (M.policyFixedPoint_spec π)
  · intro hQ
    rw [hQ]
    exact M.policyFixedPoint_spec π

theorem optimalityFixedPoint_characterization (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) :
    M.qOptimality Q = Q ↔ Q = M.optimalityFixedPoint := by
  constructor
  · intro hQ
    exact M.qOptimality_fixedpoint_unique hQ M.optimalityFixedPoint_spec
  · intro hQ
    rw [hQ]
    exact M.optimalityFixedPoint_spec

/-- Exact geometric error bound for iteration of the policy Bellman operator. -/
theorem policy_evaluation_iteration_error (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (Q₀ : State → Action → ℝ) (n : ℕ) :
    ‖(M.qBellman π)^[n] Q₀ - M.policyFixedPoint π‖ ≤
      M.discount ^ n * ‖Q₀ - M.policyFixedPoint π‖ := by
  simpa only [dist_eq_norm, coe_discountConstant] using
    StatisticalRL.Analysis.iterate_dist_le (M.qBellman_lipschitz π)
      (M.policyFixedPoint_spec π) Q₀ n

/-- Exact `γ^n` value-iteration error bound relative to the optimality fixed point. -/
theorem value_iteration_error (M : DiscountedMDP State Action)
    (Q₀ : State → Action → ℝ) (n : ℕ) :
    ‖M.qOptimality^[n] Q₀ - M.optimalityFixedPoint‖ ≤
      M.discount ^ n * ‖Q₀ - M.optimalityFixedPoint‖ := by
  simpa only [dist_eq_norm, coe_discountConstant] using
    StatisticalRL.Analysis.iterate_dist_le M.qOptimality_lipschitz
      M.optimalityFixedPoint_spec Q₀ n

theorem tendsto_policy_evaluation_iteration (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (Q₀ : State → Action → ℝ) :
    Tendsto (fun n ↦ (M.qBellman π)^[n] Q₀) atTop (𝓝 (M.policyFixedPoint π)) := by
  have heq := (M.qBellman_contracting π).fixedPoint_unique (M.policyFixedPoint_spec π)
  simpa only [← heq] using (M.qBellman_contracting π).tendsto_iterate_fixedPoint Q₀

theorem tendsto_value_iteration (M : DiscountedMDP State Action)
    (Q₀ : State → Action → ℝ) :
    Tendsto (fun n ↦ M.qOptimality^[n] Q₀) atTop (𝓝 M.optimalityFixedPoint) := by
  have heq := M.qOptimality_contracting.fixedPoint_unique M.optimalityFixedPoint_spec
  simpa only [← heq] using M.qOptimality_contracting.tendsto_iterate_fixedPoint Q₀

/-- The literal effective horizon from the source. -/
noncomputable def effectiveHorizon (M : DiscountedMDP State Action) : ℝ :=
  1 / (1 - M.discount)

theorem effectiveHorizon_nonneg (M : DiscountedMDP State Action) :
    0 ≤ M.effectiveHorizon :=
  div_nonneg zero_le_one (sub_pos.mpr M.discount_lt_one).le

theorem effectiveHorizon_recursion (M : DiscountedMDP State Action) :
    1 + M.discount * M.effectiveHorizon = M.effectiveHorizon := by
  have hne : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  have hmul : (1 - M.discount) * M.effectiveHorizon = 1 := by
    rw [effectiveHorizon, one_div, mul_inv_cancel₀ hne]
  linarith only [hmul]

/-- The policy Bellman map preserves the source's full return interval. -/
theorem qBellman_preserves_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {Q : State → Action → ℝ}
    (hQ : ∀ s a, 0 ≤ Q s a ∧ Q s a ≤ M.effectiveHorizon) (s : State) (a : Action) :
    0 ≤ M.qBellman π Q s a ∧ M.qBellman π Q s a ≤ M.effectiveHorizon := by
  have hlo (t : State) : 0 ≤ (π t).expectation (Q t) :=
    (π t).expectation_nonneg (fun b ↦ (hQ t b).1)
  have hhi (t : State) : (π t).expectation (Q t) ≤ M.effectiveHorizon :=
    (π t).expectation_le_const (fun b ↦ (hQ t b).2)
  constructor
  · exact add_nonneg (M.reward_nonneg s a)
      (mul_nonneg M.discount_nonneg ((M.transition s a).expectation_nonneg hlo))
  · calc
      M.qBellman π Q s a ≤ 1 + M.discount * M.effectiveHorizon :=
        add_le_add (M.reward_le_one s a)
          (mul_le_mul_of_nonneg_left ((M.transition s a).expectation_le_const hhi)
            M.discount_nonneg)
      _ = M.effectiveHorizon := M.effectiveHorizon_recursion

/-- The optimality Bellman map preserves the same interval, including randomized transitions. -/
theorem qOptimality_preserves_bounds (M : DiscountedMDP State Action)
    {Q : State → Action → ℝ}
    (hQ : ∀ s a, 0 ≤ Q s a ∧ Q s a ≤ M.effectiveHorizon) (s : State) (a : Action) :
    0 ≤ M.qOptimality Q s a ∧ M.qOptimality Q s a ≤ M.effectiveHorizon := by
  letI : Nonempty Action := M.action_nonempty
  have hlo (t : State) : 0 ≤ actionMaximum (Q t) :=
    (hQ t (Classical.choice M.action_nonempty)).1.trans
      (le_actionMaximum (Q t) (Classical.choice M.action_nonempty))
  have hhi (t : State) : actionMaximum (Q t) ≤ M.effectiveHorizon := by
    apply (Finset.sup'_le_iff Finset.univ_nonempty (Q t)).2
    intro b _
    exact (hQ t b).2
  constructor
  · exact add_nonneg (M.reward_nonneg s a)
      (mul_nonneg M.discount_nonneg ((M.transition s a).expectation_nonneg hlo))
  · calc
      M.qOptimality Q s a ≤ 1 + M.discount * M.effectiveHorizon :=
        add_le_add (M.reward_le_one s a)
          (mul_le_mul_of_nonneg_left ((M.transition s a).expectation_le_const hhi)
            M.discount_nonneg)
      _ = M.effectiveHorizon := M.effectiveHorizon_recursion

theorem policy_evaluation_zero_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) (s : State) (a : Action) :
    0 ≤ ((M.qBellman π)^[n] 0) s a ∧
      ((M.qBellman π)^[n] 0) s a ≤ M.effectiveHorizon := by
  induction n generalizing s a with
  | zero => exact ⟨le_refl 0, M.effectiveHorizon_nonneg⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact M.qBellman_preserves_bounds π ih s a

theorem value_iteration_zero_bounds (M : DiscountedMDP State Action)
    (n : ℕ) (s : State) (a : Action) :
    0 ≤ (M.qOptimality^[n] 0) s a ∧
      (M.qOptimality^[n] 0) s a ≤ M.effectiveHorizon := by
  induction n generalizing s a with
  | zero => exact ⟨le_refl 0, M.effectiveHorizon_nonneg⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact M.qOptimality_preserves_bounds ih s a

/-- The policy Bellman solution is in the exact source return interval. -/
theorem policyFixedPoint_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    0 ≤ M.policyFixedPoint π s a ∧ M.policyFixedPoint π s a ≤ 1 / (1 - M.discount) := by
  have hlim := M.tendsto_policy_evaluation_iteration π 0
  have hcoord := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim s)) a
  exact ⟨ge_of_tendsto' hcoord (fun n ↦ (M.policy_evaluation_zero_bounds π n s a).1),
    le_of_tendsto' hcoord (fun n ↦ (M.policy_evaluation_zero_bounds π n s a).2)⟩

/-- The optimality Bellman solution is in the exact source return interval. -/
theorem optimalityFixedPoint_bounds (M : DiscountedMDP State Action)
    (s : State) (a : Action) :
    0 ≤ M.optimalityFixedPoint s a ∧ M.optimalityFixedPoint s a ≤ 1 / (1 - M.discount) := by
  have hlim := M.tendsto_value_iteration 0
  have hcoord := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim s)) a
  exact ⟨ge_of_tendsto' hcoord (fun n ↦ (M.value_iteration_zero_bounds n s a).1),
    le_of_tendsto' hcoord (fun n ↦ (M.value_iteration_zero_bounds n s a).2)⟩

end StatisticalRL.DiscountedMDP
