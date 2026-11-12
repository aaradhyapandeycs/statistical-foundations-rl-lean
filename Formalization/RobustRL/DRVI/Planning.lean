import Formalization.RobustRL.DRVI.Optimality

/-!
# DRVI as robust value iteration; planning error (milestone 2, R0e)

Source: Algorithm `alg:cvi-dro-infinite`, `chapters/robust_RL.tex:243–289`: `Q̂_0 = 0`,
`Q̂_t = T̂^σ(Q̂_{t-1})` with the exact inner infimum, output any greedy selector of `Q̂_T`.

* `drviIterate_error`: `|Q_t(s,a) − Q⋆(s,a)| ≤ γ^t/(1-γ)` where `Q⋆ = optQ` is the robust optimal
  action value (`r + γ inf ⟨q, V⋆⟩`) of the same model.
* `greedy_residual_bounds`: for a greedy selector `f` of `Q_T`, the planning residual
  `ξ(s) = V⋆(s) − Q⋆(s, f s)` lies in `[0, 2γ^T/(1-γ)]` (plan §3.1 (P)).
* `pow_le_sq_of_iterations`: under the corrected count `T ≥ 2 log(N/(1-γ))/(1-γ)` (C37),
  `γ^T ≤ ((1-γ)/N)^2`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem robustBellman_eq_robustQ (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (Q : State → Action → ℝ) (s : State) (a : Action) :
    robustBellman ball M σ Q s a =
      robustQ (ballFamily ball M σ) M
        (fun t ↦ letI : Nonempty Action := M.action_nonempty; actionMaximum (Q t)) s a := rfl

/-- The robust optimal action value `Q⋆(s,a) = r(s,a) + γ inf_{q ∈ U s a} ⟨q, V⋆⟩`. -/
noncomputable def optQ (U : RowFamily State Action) (M : DiscountedMDP State Action) :
    State → Action → ℝ :=
  robustQ U M (optFix U M)

theorem actionMaximum_optQ (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (s : State) :
    (letI : Nonempty Action := M.action_nonempty; actionMaximum (optQ U M s)) = optFix U M s :=
  congrFun (optFix_spec U M) s

theorem optQ_le_optFix (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (s : State) (a : Action) : optQ U M s a ≤ optFix U M s := by
  letI : Nonempty Action := M.action_nonempty
  rw [← actionMaximum_optQ U M s]
  exact le_actionMaximum _ a

theorem exists_optQ_eq_optFix (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (s : State) : ∃ a, optQ U M s a = optFix U M s := by
  refine ⟨greedyAction U M (optFix U M) s, ?_⟩
  rw [optQ, ← optOp_eq_greedy, optFix_spec]

theorem optQ_bounds (U : RowFamily State Action) (hU : ∀ s a, (U s a).Nonempty)
    (M : DiscountedMDP State Action) (s : State) (a : Action) :
    0 ≤ optQ U M s a ∧ optQ U M s a ≤ 1 / (1 - M.discount) := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hb := rowInf_bounds (hU s a) (V := optFix U M) (lo := 0) (hi := 1 / (1 - M.discount))
    (fun x ↦ (optFix_bounds U hU M x).1) (fun x ↦ (optFix_bounds U hU M x).2)
  have hr0 := M.reward_nonneg s a
  have hr1 := M.reward_le_one s a
  have key : M.discount * (1 / (1 - M.discount)) = 1 / (1 - M.discount) - 1 := by
    have : 1 - M.discount ≠ 0 := by linarith
    field_simp; ring
  unfold optQ robustQ
  constructor
  · nlinarith [hb.1]
  · nlinarith [hb.2]

theorem drviIterate_zero (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ) :
    drviIterate ball M σ 0 = 0 := rfl

theorem drviIterate_succ (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (t : ℕ) : drviIterate ball M σ (t + 1) = robustBellman ball M σ (drviIterate ball M σ t) :=
  rfl

/-- Planning error of DRVI from `Q̂_0 = 0`: `|Q_t − Q⋆| ≤ γ^t/(1-γ)`. -/
theorem drviIterate_error (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (hU : ∀ s a, (ball (M.transition s a) σ).Nonempty) (t : ℕ) :
    ∀ s a, |drviIterate ball M σ t s a - optQ (ballFamily ball M σ) M s a| ≤
      M.discount ^ t / (1 - M.discount) := by
  letI : Nonempty Action := M.action_nonempty
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hpos : 0 < 1 - M.discount := by linarith
  induction t with
  | zero =>
    intro s a
    have hb := optQ_bounds (ballFamily ball M σ) hU M s a
    rw [drviIterate_zero, pow_zero]
    simp only [Pi.zero_apply, zero_sub, abs_neg]
    rw [abs_of_nonneg hb.1]
    exact hb.2
  | succ t ih =>
    intro s a
    rw [drviIterate_succ, robustBellman_eq_robustQ]
    have hc : 0 ≤ M.discount ^ t / (1 - M.discount) := div_nonneg (pow_nonneg hγ0 t) hpos.le
    have hV : ∀ x, |actionMaximum (drviIterate ball M σ t x) - optFix (ballFamily ball M σ) M x|
        ≤ M.discount ^ t / (1 - M.discount) := by
      intro x
      rw [← actionMaximum_optQ (ballFamily ball M σ) M x]
      exact abs_actionMaximum_sub_le (ih x)
    have hrow := abs_rowInf_sub_le (ballFamily ball M σ s a) hc hV
    unfold optQ robustQ
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hγ0]
    calc M.discount * |rowInf (ballFamily ball M σ s a) (fun x ↦ actionMaximum
          (drviIterate ball M σ t x)) - rowInf (ballFamily ball M σ s a)
          (optFix (ballFamily ball M σ) M)|
        ≤ M.discount * (M.discount ^ t / (1 - M.discount)) :=
          mul_le_mul_of_nonneg_left hrow hγ0
      _ = M.discount ^ (t + 1) / (1 - M.discount) := by ring

/-- Greedy planning residual (plan §3.1 (P)): for any greedy selector `f` of `Q_T`,
`ξ(s) = V⋆(s) − Q⋆(s, f s) ∈ [0, 2γ^T/(1-γ)]`. -/
theorem greedy_residual_bounds (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (hU : ∀ s a, (ball (M.transition s a) σ).Nonempty) (T : ℕ) {f : State → Action}
    (hf : IsGreedy (drviIterate ball M σ T) f) (s : State) :
    0 ≤ optFix (ballFamily ball M σ) M s - optQ (ballFamily ball M σ) M s (f s) ∧
      optFix (ballFamily ball M σ) M s - optQ (ballFamily ball M σ) M s (f s) ≤
        2 * (M.discount ^ T / (1 - M.discount)) := by
  set U := ballFamily ball M σ
  constructor
  · have := optQ_le_optFix U M s (f s)
    linarith
  · obtain ⟨a, ha⟩ := exists_optQ_eq_optFix U M s
    have e1 := abs_le.mp (drviIterate_error ball M σ hU T s a)
    have e2 := abs_le.mp (drviIterate_error ball M σ hU T s (f s))
    have hg := hf s a
    linarith [e1.1, e2.2]

/-- Corrected iteration count (C37): `T ≥ 2 log(N/(1-γ))/(1-γ)` gives `γ^T ≤ ((1-γ)/N)^2`. -/
theorem pow_le_sq_of_iterations {γ N : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hN : 0 < N) {T : ℕ}
    (hT : 2 * Real.log (N / (1 - γ)) / (1 - γ) ≤ T) : γ ^ T ≤ ((1 - γ) / N) ^ 2 := by
  have hpos : 0 < 1 - γ := by linarith
  have hT' : 2 * Real.log (N / (1 - γ)) ≤ T * (1 - γ) := by
    rwa [div_le_iff₀ hpos] at hT
  have hlogγ : Real.log γ ≤ γ - 1 := Real.log_le_sub_one_of_pos hγ0
  have hlhs : Real.log (γ ^ T) ≤ -(T * (1 - γ)) := by
    rw [Real.log_pow]
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  have hrhs : Real.log (((1 - γ) / N) ^ 2) = -(2 * Real.log (N / (1 - γ))) := by
    rw [Real.log_pow, Real.log_div hpos.ne' hN.ne', Real.log_div hN.ne' hpos.ne']
    push_cast; ring
  have h1 : 0 < γ ^ T := pow_pos hγ0 T
  have h2 : 0 < ((1 - γ) / N) ^ 2 := by positivity
  rw [← Real.log_le_log_iff h1 h2, hrhs]
  linarith

end StatisticalRL.RobustRL.DRVI
