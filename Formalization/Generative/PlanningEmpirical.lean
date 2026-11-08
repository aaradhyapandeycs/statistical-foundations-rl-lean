import Formalization.MDP.PlanningIterationCount
import Formalization.Generative.ModelBasedPolicyLearning
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Empirical VI/PI reach the planner slack of Theorem 3.2 (MB:943, claim (B))

Explicit iteration counts `k ≥ log(2N/(1−γ))/(1−γ)` for VI (from any `Q₀` with
entries in `[0, 1/(1−γ)]`) and for PI (any initial policy, arbitrary greedy
ties), and the `O((1−γ)⁻¹ log(N/(1−γ)))` form with universal constant `4`.

Composition remark (claims (A) and (B) together): the conclusions here are
exactly the slack premise `‖V̂⋆ − V̂^π‖ ≤ 1/(N(1−γ))` of
`mainSample_policyLearning_approx`, which holds for every deterministic `f`
inside one sampling event. So on that event, the greedy output of empirical VI
after the stated number of iterations, and the PI policy `π k` (deterministic
for `k ≥ 1`), satisfy the V and Q guarantees of Theorem 3.2 under the printed
budget with `c₀ = 10240`. No separate theorem is stated for this composition. -/

namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A pointwise value-loss bound is a sup-norm bound on `V⋆ − V^π`. -/
theorem optimalGreedy_value_gap_norm_le (H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (c : ℝ)
    (hloss : ∀ s, H.trajectoryExpectedValue H.optimalGreedyPolicy s -
      H.trajectoryExpectedValue π s ≤ c) :
    ‖H.trajectoryExpectedValue H.optimalGreedyPolicy - H.trajectoryExpectedValue π‖ ≤ c := by
  have hc : 0 ≤ c := by
    obtain ⟨s⟩ := H.state_nonempty
    exact (sub_nonneg.mpr (H.trajectoryValue_le_optimalGreedy π s)).trans (hloss s)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  rw [Real.norm_eq_abs, Pi.sub_apply,
    abs_of_nonneg (sub_nonneg.mpr (H.trajectoryValue_le_optimalGreedy π s))]
  exact hloss s

/-- Every policy is within `1/(1−γ)` of optimal. -/
theorem optimalGreedy_value_gap_le_horizon (H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    H.trajectoryExpectedValue H.optimalGreedyPolicy s - H.trajectoryExpectedValue π s ≤
      1 / (1 - H.discount) := by
  have h1 := (H.trajectoryExpectedValue_bounds H.optimalGreedyPolicy s).2
  have h2 := (H.trajectoryExpectedValue_bounds π s).1
  linarith

/-- Scalar step: `2 (γ^k · C)/(1−γ) ≤ 1/(n(1−γ))` when `C ≤ 1/(1−γ)` and
`γ^k ≤ (1−γ)/(2n)`. -/
theorem planning_loss_scalar (γ n C : ℝ) (k : ℕ) (hγ1 : γ < 1) (hn : 0 < n)
    (hC0 : 0 ≤ C) (hC : C ≤ 1 / (1 - γ)) (hpow : γ ^ k ≤ (1 - γ) / (2 * n)) :
    2 * (γ ^ k * C) / (1 - γ) ≤ 1 / (n * (1 - γ)) := by
  have hh : 0 < 1 - γ := sub_pos.mpr hγ1
  have hm : γ ^ k * C ≤ (1 - γ) / (2 * n) * (1 / (1 - γ)) :=
    mul_le_mul hpow hC hC0 (by positivity)
  have he : (1 - γ) / (2 * n) * (1 / (1 - γ)) = 1 / (2 * n) := by
    field_simp
  rw [he] at hm
  calc
    2 * (γ ^ k * C) / (1 - γ) ≤ 2 * (1 / (2 * n)) / (1 - γ) := by gcongr
    _ = 1 / (n * (1 - γ)) := by field_simp

/-- **VI, explicit count.** From any `Q₀` with entries in `[0, 1/(1−γ)]`, after
`k ≥ log(2n/(1−γ))/(1−γ)` iterations any greedy policy of the iterate is
within `1/(n(1−γ))` of optimal. -/
theorem valueIteration_value_loss_le (H : DiscountedMDP State Action)
    (Q₀ : State → Action → ℝ) (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - H.discount))
    (n : ℝ) (hn : 0 < n) (k : ℕ)
    (hk : Real.log (2 * n / (1 - H.discount)) / (1 - H.discount) ≤ k)
    (f : State → Action)
    (hgreedy : letI : Nonempty Action := H.action_nonempty
      ∀ s, (H.qOptimality^[k] Q₀) s (f s) = actionMaximum ((H.qOptimality^[k] Q₀) s)) :
    ‖H.trajectoryExpectedValue H.optimalGreedyPolicy -
      H.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
      1 / (n * (1 - H.discount)) := by
  apply H.optimalGreedy_value_gap_norm_le
  intro s
  refine (H.valueIteration_greedy_value_loss Q₀ k f hgreedy s).trans ?_
  exact planning_loss_scalar H.discount n _ k H.discount_lt_one hn
    (norm_nonneg _)
    (H.norm_sub_le_of_qfun_bounds _ _ hQ₀ H.optimalityFixedPoint_bounds)
    (discount_pow_le_of_log_le H.discount n k H.discount_nonneg H.discount_lt_one hn hk)

/-- **PI, explicit count.** With any initial policy and arbitrary greedy ties,
for `k ≥ log(2n/(1−γ))/(1−γ)` the policy `π (k+1)` is within `1/(n(1−γ))` of
optimal. -/
theorem policyIteration_value_loss_le (H : DiscountedMDP State Action)
    (π : ℕ → StationaryPolicy State Action) (g : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (g n s))
    (hmax : letI : Nonempty Action := H.action_nonempty
      ∀ n s, H.policyFixedPoint (π n) s (g n s) = actionMaximum (H.policyFixedPoint (π n) s))
    (n : ℝ) (hn : 0 < n) (k : ℕ)
    (hk : Real.log (2 * n / (1 - H.discount)) / (1 - H.discount) ≤ k) :
    ‖H.trajectoryExpectedValue H.optimalGreedyPolicy - H.trajectoryExpectedValue (π (k + 1))‖ ≤
      1 / (n * (1 - H.discount)) := by
  apply H.optimalGreedy_value_gap_norm_le
  intro s
  refine (H.policyIteration_value_loss π g hupdate hmax k s).trans ?_
  exact planning_loss_scalar H.discount n _ k H.discount_lt_one hn
    (norm_nonneg _)
    (H.norm_sub_le_of_qfun_bounds _ _ (H.policyFixedPoint_bounds (π 0))
      H.optimalityFixedPoint_bounds)
    (discount_pow_le_of_log_le H.discount n k H.discount_nonneg H.discount_lt_one hn hk)

end StatisticalRL.DiscountedMDP

namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP

/-- The `O((1−γ)⁻¹ log(N/(1−γ)))` iteration claim (MB:943, (B)) on the
empirical model, with universal constant `C = 4`. For `N = 1` the slack
`1/(1−γ)` holds for every policy; for `N ≥ 2`, `4 log(N/(1−γ))/(1−γ)`
dominates the explicit counts above (for PI, after subtracting one). -/
theorem empirical_planningIterations :
    ∃ C : ℝ, 0 < C ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
        (data : Samples State Action N),
      letI : Nonempty Action := M.action_nonempty
      (∀ Q₀ : State → Action → ℝ,
        (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) →
        ∀ k : ℕ, C / (1 - M.discount) * Real.log (N / (1 - M.discount)) ≤ k →
        ∀ f : State → Action,
          (∀ s, ((empiricalModel M N hN data).qOptimality^[k] Q₀) s (f s) =
            actionMaximum (((empiricalModel M N hN data).qOptimality^[k] Q₀) s)) →
          ‖valueEstimator M N hN data - (empiricalModel M N hN data).trajectoryExpectedValue
              (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 1 / (N * (1 - M.discount))) ∧
      (∀ (π : ℕ → StationaryPolicy State Action) (g : ℕ → State → Action),
        (∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (g n s)) →
        (∀ n s, (empiricalModel M N hN data).policyFixedPoint (π n) s (g n s) =
          actionMaximum ((empiricalModel M N hN data).policyFixedPoint (π n) s)) →
        ∀ k : ℕ, 1 ≤ k → C / (1 - M.discount) * Real.log (N / (1 - M.discount)) ≤ k →
          ‖valueEstimator M N hN data -
            (empiricalModel M N hN data).trajectoryExpectedValue (π k)‖ ≤
            1 / (N * (1 - M.discount))) := by
  refine ⟨4, by norm_num, ?_⟩
  intro State Action _ _ M N hN data
  letI : Nonempty Action := M.action_nonempty
  let H := empiricalModel M N hN data
  have hV : valueEstimator M N hN data = H.trajectoryExpectedValue H.optimalGreedyPolicy := rfl
  have hγ : H.discount = M.discount := rfl
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hh1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hV]
  by_cases hN1 : N = 1
  · -- With one sample per row the slack is the horizon, which every policy meets.
    subst hN1
    have htriv (π : StationaryPolicy State Action) :
        ‖H.trajectoryExpectedValue H.optimalGreedyPolicy - H.trajectoryExpectedValue π‖ ≤
          1 / ((1 : ℕ) * (1 - M.discount)) := by
      rw [Nat.cast_one, one_mul]
      exact H.optimalGreedy_value_gap_norm_le π _ (H.optimalGreedy_value_gap_le_horizon π)
    exact ⟨fun _ _ _ _ f _ ↦ htriv _, fun π _ _ _ k _ _ ↦ htriv (π k)⟩
  · have hN2 : (2 : ℝ) ≤ N := by
      have : 2 ≤ N := by omega
      exact_mod_cast this
    set L := Real.log (N / (1 - M.discount)) with hLdef
    have hNh : (2 : ℝ) ≤ N / (1 - M.discount) := by
      rw [le_div_iff₀ hh]
      nlinarith
    have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hNh
    have hlog2 := Real.log_two_gt_d9
    have hsplit : Real.log (2 * N / (1 - M.discount)) = Real.log 2 + L := by
      rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
    have hcount (k : ℕ) (hk : 4 / (1 - M.discount) * L ≤ k) : 4 * L ≤ k * (1 - M.discount) := by
      rw [show 4 / (1 - M.discount) * L = 4 * L / (1 - M.discount) by ring,
        div_le_iff₀ hh] at hk
      exact hk
    constructor
    · intro Q₀ hQ₀ k hk f hf
      have hk4 := hcount k hk
      have hk' : Real.log (2 * N / (1 - H.discount)) / (1 - H.discount) ≤ k := by
        rw [hγ, hsplit, div_le_iff₀ hh]
        linarith
      exact H.valueIteration_value_loss_le Q₀ hQ₀ N hn k hk' f hf
    · intro π g hupdate hmax k hk1 hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk1
      have hk4 := hcount (j + 1) hk
      push_cast at hk4
      have hj : Real.log (2 * N / (1 - H.discount)) / (1 - H.discount) ≤ j := by
        rw [hγ, hsplit, div_le_iff₀ hh]
        nlinarith
      exact H.policyIteration_value_loss_le π g hupdate hmax N hn j hj

end StatisticalRL.ModelBasedPolicyLearning
