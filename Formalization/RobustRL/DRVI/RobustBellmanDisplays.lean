import Formalization.RobustRL.DRVI.RobustQ
import Formalization.RobustRL.DRVI.Planning

/-!
# Robust Bellman equations, the robust Bellman operator and DRVI (displays)

Source: `chapters/robust_RL.tex:102–133` (display `eq:bellman-equ-infinite-all`, the operator
`eq:robust_bellman`, "`Q^{⋆,σ}` is the unique fixed point of `T^σ`", "`γ`-contraction", geometric
convergence of DRVI) and `:261–262` (the same for the empirical operator `T̂^σ`, which is the
operator of the empirical nominal kernel).

All statements concern the actual trajectory objects `robustPolicyValue` / `robustPolicyQ`
(infimum over admissible kernels of the actual infinite-trajectory value, static adversary) of
`Ch7Definitions`. The optimal objects are taken in two forms:

* `V⋆ = robustOptimalValue` (supremum over stationary randomized policies) and
  `Q⋆ = sSup_π Q^{π,σ}`;
* `V^{π⋆,σ}`, `Q^{π⋆,σ}` for an *arbitrary* stationary policy `π⋆` that maximizes the robust value
  at every state (`robust_RL.tex:90–98`).

The two agree (`robustPolicyQ_eq_optQ_of_dominates`, `sSup_robustPolicyQ_eq_optQ`).
For a row family whose rows attain their infima (TV and χ² balls, `σ ≥ 0`), the robust Bellman
operator `T^σ Q (s,a) = r(s,a) + γ inf_{q ∈ U^σ(P^0_{s,a})} ⟨q, max_b Q(·,b)⟩` has `Q⋆` as its
unique fixed point, is a `γ`-contraction in the sup norm, and its iterates from any start converge
geometrically to `Q⋆`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-! ## Inline forms of the row infimum and the action maximum -/

/-- The exact row infimum as an indexed infimum over the row set. -/
theorem rowInf_eq_iInf (U : Set (FiniteDistribution State)) (V : State → ℝ) :
    rowInf U V = ⨅ q : U, ∑ s', q.1.prob s' * V s' := by
  unfold rowInf
  rw [Set.image_eq_range]
  rfl

/-- The finite action maximum as an indexed supremum. -/
theorem actionMaximum_eq_iSup [Nonempty Action] (f : Action → ℝ) :
    actionMaximum f = ⨆ b, f b :=
  Finset.sup'_univ_eq_ciSup f

/-- The robust Bellman operator `T^σ` written out (`robust_RL.tex:118–131`). -/
theorem robustBellman_eq_inline (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (Q : State → Action → ℝ) :
    robustBellman ball M σ Q = fun s a ↦ M.reward s a + M.discount *
      ⨅ q : ball (M.transition s a) σ, ∑ s', q.1.prob s' * ⨆ b, Q s' b := by
  letI : Nonempty Action := M.action_nonempty
  funext s a
  unfold robustBellman
  rw [rowRobustInf_eq_rowInf, rowInf_eq_iInf]
  simp only [actionMaximum_eq_iSup]

/-! ## Robust Bellman consistency, inline form -/

/-- `eq:bellman-equ-pi-infinite` with the infimum written over the row ball. -/
theorem robustPolicyQ_eq_reward_add_iInf (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    robustPolicyQ ball M σ π s a = M.reward s a + M.discount *
      ⨅ q : ball (M.transition s a) σ, ∑ s', q.1.prob s' * robustPolicyValue ball M σ π s' := by
  rw [robustPolicyQ_eq_reward_add_rowInf ball M σ hU π s a, rowInf_eq_iInf]

/-! ## Robust-optimal policies -/

/-- Any stationary policy maximizing the robust value at every state has robust value `optFix`. -/
theorem robustPolicyValue_eq_optFix_of_dominates (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (πs : StationaryPolicy State Action)
    (h : ∀ (π : StationaryPolicy State Action) (s : State),
      robustPolicyValue ball M σ π s ≤ robustPolicyValue ball M σ πs s) :
    robustPolicyValue ball M σ πs = optFix (ballFamily ball M σ) M := by
  funext s
  apply le_antisymm
  · rw [robustPolicyValue_eq_policyFix ball M σ hU]
    exact policyFix_le_optFix _ M πs s
  · have h1 := h (detPolicy (optPolicy (ballFamily ball M σ) M)) s
    rw [robustPolicyValue_eq_policyFix ball M σ hU (detPolicy _), policyFix_optPolicy] at h1
    exact h1

/-- Any stationary policy maximizing the robust value has robust Q-function `optQ`. -/
theorem robustPolicyQ_eq_optQ_of_dominates (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (πs : StationaryPolicy State Action)
    (h : ∀ (π : StationaryPolicy State Action) (s : State),
      robustPolicyValue ball M σ π s ≤ robustPolicyValue ball M σ πs s) :
    robustPolicyQ ball M σ πs = optQ (ballFamily ball M σ) M := by
  funext s a
  rw [robustPolicyQ_eq_reward_add_rowInf ball M σ hU πs s a,
    robustPolicyValue_eq_optFix_of_dominates ball M σ hU πs h]
  rfl

/-- `Q⋆ = max_π Q^{π,σ}`: the supremum of the robust Q-functions of all stationary randomized
policies is `optQ`, attained by the deterministic policy `optPolicy`. -/
theorem sSup_robustPolicyQ_eq_optQ (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (s : State) (a : Action) :
    sSup (Set.range fun π : StationaryPolicy State Action ↦ robustPolicyQ ball M σ π s a) =
      optQ (ballFamily ball M σ) M s a := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨detPolicy (optPolicy (ballFamily ball M σ) M), robustPolicyQ_optPolicy ball M σ hU s a⟩
  · rintro _ ⟨π, rfl⟩
    exact robustPolicyQ_le_robustQ_optFix ball M σ hU π s a

/-- `eq:bellman-equ-star-infinite` for the supremum objects:
`max_π Q^{π,σ}(s,a) = r(s,a) + γ inf_{q ∈ U^σ(P^0_{s,a})} ⟨q, V^{⋆,σ}⟩`. -/
theorem sSup_robustPolicyQ_eq_reward_add_iInf (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (s : State) (a : Action) :
    sSup (Set.range fun π : StationaryPolicy State Action ↦ robustPolicyQ ball M σ π s a) =
      M.reward s a + M.discount *
        ⨅ q : ball (M.transition s a) σ, ∑ s', q.1.prob s' * robustOptimalValue ball M σ s' := by
  rw [sSup_robustPolicyQ_eq_optQ ball M σ hU, robustOptimalValue_eq_optFix ball M σ hU,
    ← rowInf_eq_iInf]
  rfl

/-! ## The robust Bellman operator: fixed point, uniqueness, contraction -/

/-- `optQ` is a fixed point of the robust Bellman operator. -/
theorem robustBellman_optQ (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ) :
    robustBellman ball M σ (optQ (ballFamily ball M σ) M) = optQ (ballFamily ball M σ) M := by
  funext s a
  rw [robustBellman_eq_robustQ]
  have hV : (fun t ↦ (letI : Nonempty Action := M.action_nonempty;
      actionMaximum (optQ (ballFamily ball M σ) M t))) = optFix (ballFamily ball M σ) M :=
    funext (actionMaximum_optQ (ballFamily ball M σ) M)
  rw [hV]
  rfl

/-- Every fixed point of the robust Bellman operator is `optQ`. -/
theorem eq_optQ_of_robustBellman (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    {Q : State → Action → ℝ} (hQ : robustBellman ball M σ Q = Q) :
    Q = optQ (ballFamily ball M σ) M := by
  letI : Nonempty Action := M.action_nonempty
  set U := ballFamily ball M σ
  set V : State → ℝ := fun t ↦ actionMaximum (Q t) with hVdef
  have hTQ : ∀ s a, robustQ U M V s a = Q s a := by
    intro s a
    rw [← hQ, robustBellman_eq_robustQ]
  have hfix : optOp U M V = V := by
    funext s
    unfold optOp
    have : robustQ U M V s = Q s := funext (hTQ s)
    rw [this]
  have hVeq : V = optFix U M := eq_optFix U M hfix
  funext s a
  rw [← hTQ s a, hVeq]
  rfl

/-- Pointwise `γ`-contraction of the robust Bellman operator. -/
theorem abs_robustBellman_sub_le (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    {Q Q' : State → Action → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ s a, |Q s a - Q' s a| ≤ c)
    (s : State) (a : Action) :
    |robustBellman ball M σ Q s a - robustBellman ball M σ Q' s a| ≤ M.discount * c := by
  letI : Nonempty Action := M.action_nonempty
  have hγ0 := M.discount_nonneg
  unfold robustBellman
  rw [rowRobustInf_eq_rowInf, rowRobustInf_eq_rowInf, add_sub_add_left_eq_sub, ← mul_sub,
    abs_mul, abs_of_nonneg hγ0]
  apply mul_le_mul_of_nonneg_left _ hγ0
  exact abs_rowInf_sub_le _ hc (fun t ↦ abs_actionMaximum_sub_le (h t))

/-- `γ`-contraction of the robust Bellman operator in the sup norm. -/
theorem norm_robustBellman_sub_le (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (Q Q' : State → Action → ℝ) :
    ‖robustBellman ball M σ Q - robustBellman ball M σ Q'‖ ≤ M.discount * ‖Q - Q'‖ := by
  have hγ0 := M.discount_nonneg
  have hc : 0 ≤ ‖Q - Q'‖ := norm_nonneg _
  have h : ∀ s a, |Q s a - Q' s a| ≤ ‖Q - Q'‖ := by
    intro s a
    have h1 : ‖(Q - Q') s a‖ ≤ ‖(Q - Q') s‖ := norm_le_pi_norm ((Q - Q') s) a
    have h2 : ‖(Q - Q') s‖ ≤ ‖Q - Q'‖ := norm_le_pi_norm (Q - Q') s
    rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs] at h1
    exact h1.trans (by rw [Pi.sub_apply] at h2; exact h2)
  have hpos : 0 ≤ M.discount * ‖Q - Q'‖ := mul_nonneg hγ0 hc
  refine (pi_norm_le_iff_of_nonneg hpos).2 fun s ↦ (pi_norm_le_iff_of_nonneg hpos).2 fun a ↦ ?_
  rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs]
  exact abs_robustBellman_sub_le ball M σ hc h s a

/-- Geometric convergence of the iterates of `T^σ` from an arbitrary initialization to a fixed
point. -/
theorem norm_robustBellman_iterate_sub_le (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) {Qs : State → Action → ℝ} (hQs : robustBellman ball M σ Qs = Qs)
    (Q₀ : State → Action → ℝ) (t : ℕ) :
    ‖(robustBellman ball M σ)^[t] Q₀ - Qs‖ ≤ M.discount ^ t * ‖Q₀ - Qs‖ := by
  have hγ0 := M.discount_nonneg
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    calc ‖robustBellman ball M σ ((robustBellman ball M σ)^[t] Q₀) - Qs‖
        = ‖robustBellman ball M σ ((robustBellman ball M σ)^[t] Q₀) -
            robustBellman ball M σ Qs‖ := by rw [hQs]
      _ ≤ M.discount * ‖(robustBellman ball M σ)^[t] Q₀ - Qs‖ :=
          norm_robustBellman_sub_le ball M σ _ _
      _ ≤ M.discount * (M.discount ^ t * ‖Q₀ - Qs‖) := mul_le_mul_of_nonneg_left ih hγ0
      _ = M.discount ^ (t + 1) * ‖Q₀ - Qs‖ := by ring

/-- The DRVI iterates are the iterates of `T^σ` from `0`. -/
theorem drviIterate_eq_iterate (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (t : ℕ) : drviIterate ball M σ t = (robustBellman ball M σ)^[t] 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [drviIterate_succ, ih, Function.iterate_succ_apply']

end StatisticalRL.RobustRL.DRVI
