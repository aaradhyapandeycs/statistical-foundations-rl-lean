import Formalization.MDP.PolicyIteration
import Formalization.MDP.FixedPoint

/-! # Greedy-policy value loss and VI/PI iteration counts

Supporting claim (B) of the prose paragraph
`source/upstream/tex/chapters/generative_model_model_based.tex:943`: value
iteration and policy iteration reach an `η`-optimal deterministic policy in
`O((1−γ)⁻¹ log(·))` iterations. The source states this without proof; the
argument here is the standard one:

* `greedy_value_loss`: a policy greedy for `Q` with `‖Q − Q⋆‖ ≤ ξ` loses at
  most `2ξ/(1−γ)` in value (Singh–Yee);
* the linear convergence of VI and PI (`value_iteration_error`,
  `arbitraryGreedyPolicyIteration_error`, Lemma 2.1);
* `discount_pow_le_of_log_le`: `γ^k ≤ (1−γ)/(2n)` once
  `k ≥ log(2n/(1−γ))/(1−γ)`. -/

namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Pointwise entry bound from the sup norm on `State → Action → ℝ`. -/
theorem abs_apply_le_norm_of_qfun (Q : State → Action → ℝ) (s : State) (a : Action) :
    |Q s a| ≤ ‖Q‖ := by
  have h1 := norm_le_pi_norm Q s
  have h2 := norm_le_pi_norm (Q s) a
  rw [Real.norm_eq_abs] at h2
  exact h2.trans h1

/-- The optimal trajectory value at a state is the action maximum of `Q⋆`. -/
theorem trajectoryExpectedValue_optimalGreedy_eq (M : DiscountedMDP State Action) (s : State) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (M.optimalityFixedPoint s) := by
  letI : Nonempty Action := M.action_nonempty
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation
    (M.trajectoryExpectedQ M.optimalGreedyPolicy s) = _
  rw [EnvironmentStage.expectation_pointMass, M.optimalGreedy_trajectoryQ,
    M.optimalGreedyAction_max]

/-- A deterministic policy's trajectory value is its Q fixed point at its own action. -/
theorem trajectoryExpectedValue_pointMass_eq (M : DiscountedMDP State Action)
    (f : State → Action) (s : State) :
    M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s =
      M.policyFixedPoint (fun t ↦ EnvironmentStage.pointMass (f t)) s (f s) := by
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  rw [EnvironmentStage.expectation_pointMass, M.trajectoryExpectedQ_eq_policyFixedPoint]

/-- Two Q functions with entries in `[0, 1/(1−γ)]` are within `1/(1−γ)`. -/
theorem norm_sub_le_of_qfun_bounds (M : DiscountedMDP State Action)
    (Q R : State → Action → ℝ)
    (hQ : ∀ s a, 0 ≤ Q s a ∧ Q s a ≤ 1 / (1 - M.discount))
    (hR : ∀ s a, 0 ≤ R s a ∧ R s a ≤ 1 / (1 - M.discount)) :
    ‖Q - R‖ ≤ 1 / (1 - M.discount) := by
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro a
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply, abs_le]
  constructor <;> linarith [hQ s a, hR s a]

/-- **Greedy-policy value loss.** If `f` is greedy for `Q` and
`‖Q − Q⋆‖ ≤ ξ`, then `V⋆ − V^f ≤ 2ξ/(1−γ)` at every state. -/
theorem greedy_value_loss (M : DiscountedMDP State Action) (Q : State → Action → ℝ)
    (f : State → Action) (ξ : ℝ)
    (hgreedy : letI : Nonempty Action := M.action_nonempty
      ∀ s, Q s (f s) = actionMaximum (Q s))
    (hξ : ‖Q - M.optimalityFixedPoint‖ ≤ ξ) (s : State) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤
      2 * ξ / (1 - M.discount) := by
  letI : Nonempty Action := M.action_nonempty
  let π : StationaryPolicy State Action := fun t ↦ EnvironmentStage.pointMass (f t)
  let Qs := M.optimalityFixedPoint
  let Qf := M.policyFixedPoint π
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hγ := M.discount_nonneg
  have hQ (t : State) (a : Action) : |Q t a - Qs t a| ≤ ξ :=
    (abs_apply_le_norm_of_qfun (Q - Qs) t a).trans hξ
  -- The one-step greedy residual is at most `2ξ`.
  have hres (t : State) : actionMaximum (Qs t) - Qs t (f t) ≤ 2 * ξ := by
    have hm := abs_actionMaximum_sub_le (f := Qs t) (g := Q t) (ε := ξ)
      (fun a ↦ by rw [abs_sub_comm]; exact hQ t a)
    have hm' := (abs_le.mp hm).2
    have h3 := (abs_le.mp (hQ t (f t))).2
    have h4 : Q t (f t) = actionMaximum (Q t) := hgreedy t
    rw [← h4] at hm'
    linarith
  -- Bellman identities.
  have hQs (t : State) (a : Action) : Qs t a =
      M.reward t a + M.discount * (M.transition t a).expectation
        (fun u ↦ actionMaximum (Qs u)) := by
    have h := congrFun (congrFun M.optimalityFixedPoint_spec t) a
    exact h.symm
  have hQf (t : State) (a : Action) : Qf t a =
      M.reward t a + M.discount * (M.transition t a).expectation
        (fun u ↦ Qf u (f u)) := by
    have h := congrFun (congrFun (M.policyFixedPoint_spec π) t) a
    show M.policyFixedPoint π t a = M.reward t a + M.discount *
      (M.transition t a).expectation (fun u ↦ M.policyFixedPoint π u (f u))
    conv_lhs => rw [← h]
    unfold qBellman
    simp only [π, EnvironmentStage.expectation_pointMass]
  have hle (t : State) (a : Action) : Qf t a ≤ Qs t a := M.policyFixedPoint_le_optimal π t a
  -- The Q gap `D = ‖Q⋆ − Q^f‖` satisfies `D ≤ γ (2ξ + D)`.
  set D := ‖Qs - Qf‖ with hD
  have hgap (t : State) : actionMaximum (Qs t) - Qf t (f t) ≤ 2 * ξ + D := by
    have h := abs_apply_le_norm_of_qfun (Qs - Qf) t (f t)
    rw [Pi.sub_apply, Pi.sub_apply] at h
    have h' := le_abs_self (Qs t (f t) - Qf t (f t))
    linarith [hres t]
  have hstep (t : State) (a : Action) : Qs t a - Qf t a ≤ M.discount * (2 * ξ + D) := by
    rw [hQs t a, hQf t a]
    have he : M.reward t a + M.discount * (M.transition t a).expectation
          (fun u ↦ actionMaximum (Qs u)) -
        (M.reward t a + M.discount * (M.transition t a).expectation (fun u ↦ Qf u (f u))) =
        M.discount * (M.transition t a).expectation
          (fun u ↦ actionMaximum (Qs u) - Qf u (f u)) := by
      rw [FiniteDistribution.expectation_sub]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left
      ((M.transition t a).expectation_le_const hgap) hγ
  have hξ0 : 0 ≤ ξ := (norm_nonneg _).trans hξ
  have hDle : D ≤ M.discount * (2 * ξ + D) := by
    rw [hD]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro t
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro a
    rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply, abs_of_nonneg (sub_nonneg.mpr (hle t a))]
    exact hstep t a
  have hDb : (1 - M.discount) * D ≤ 2 * M.discount * ξ := by linarith
  -- Conclude for the state value.
  rw [M.trajectoryExpectedValue_optimalGreedy_eq, M.trajectoryExpectedValue_pointMass_eq]
  change actionMaximum (Qs s) - Qf s (f s) ≤ 2 * ξ / (1 - M.discount)
  rw [le_div_iff₀ hh]
  have hg := hgap s
  nlinarith [mul_le_mul_of_nonneg_left hg hh.le]

/-- **Value iteration.** The greedy policy of the `k`-th VI iterate loses at
most `2 γ^k ‖Q₀ − Q⋆‖/(1−γ)`. -/
theorem valueIteration_greedy_value_loss (M : DiscountedMDP State Action)
    (Q₀ : State → Action → ℝ) (k : ℕ) (f : State → Action)
    (hgreedy : letI : Nonempty Action := M.action_nonempty
      ∀ s, (M.qOptimality^[k] Q₀) s (f s) = actionMaximum ((M.qOptimality^[k] Q₀) s))
    (s : State) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤
      2 * (M.discount ^ k * ‖Q₀ - M.optimalityFixedPoint‖) / (1 - M.discount) :=
  M.greedy_value_loss _ f _ hgreedy (M.value_iteration_error Q₀ k) s

/-- **Policy iteration.** With arbitrary initial policy and arbitrary greedy
tie choices, the `(n+1)`-st PI policy loses at most
`2 γ^n ‖Q^{π₀} − Q⋆‖/(1−γ)`. -/
theorem policyIteration_value_loss (M : DiscountedMDP State Action)
    (π : ℕ → StationaryPolicy State Action) (g : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (g n s))
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.policyFixedPoint (π n) s (g n s) = actionMaximum (M.policyFixedPoint (π n) s))
    (n : ℕ) (s : State) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s - M.trajectoryExpectedValue (π (n + 1)) s ≤
      2 * (M.discount ^ n * ‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖) /
        (1 - M.discount) := by
  rw [hupdate n]
  exact M.greedy_value_loss _ (g n) _ (fun s ↦ hmax n s)
    (M.arbitraryGreedyPolicyIteration_error π g hupdate hmax n) s

end StatisticalRL.DiscountedMDP

namespace StatisticalRL

/-- Iteration count: for `0 ≤ γ < 1`, `n > 0`, and
`k ≥ log(2n/(1−γ))/(1−γ)`, one has `γ^k ≤ (1−γ)/(2n)`. Uses
`γ ≤ exp(γ − 1)`; the case `γ = 0` needs no separate treatment. -/
theorem discount_pow_le_of_log_le (γ n : ℝ) (k : ℕ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hn : 0 < n) (hk : Real.log (2 * n / (1 - γ)) / (1 - γ) ≤ k) :
    γ ^ k ≤ (1 - γ) / (2 * n) := by
  have hh : 0 < 1 - γ := sub_pos.mpr hγ1
  have hexp : γ ≤ Real.exp (γ - 1) := by
    have := Real.add_one_le_exp (γ - 1)
    linarith
  have hpow : γ ^ k ≤ Real.exp (γ - 1) ^ k := pow_le_pow_left₀ hγ hexp k
  rw [← Real.exp_nat_mul] at hpow
  have hk' : Real.log (2 * n / (1 - γ)) ≤ k * (1 - γ) := (div_le_iff₀ hh).1 hk
  have harg : (k : ℝ) * (γ - 1) ≤ Real.log ((1 - γ) / (2 * n)) := by
    rw [show (1 - γ) / (2 * n) = (2 * n / (1 - γ))⁻¹ by rw [inv_div], Real.log_inv]
    linarith
  calc
    γ ^ k ≤ Real.exp (k * (γ - 1)) := hpow
    _ ≤ Real.exp (Real.log ((1 - γ) / (2 * n))) := Real.exp_le_exp.mpr harg
    _ = (1 - γ) / (2 * n) := Real.exp_log (by positivity)

end StatisticalRL
