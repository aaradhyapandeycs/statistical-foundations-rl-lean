import Formalization.RobustRL.DRVI.Optimality
import Formalization.RobustRL.LowerBounds.Ch7Definitions

/-!
# A deterministic policy maximizes the robust value and the robust Q-function

Source: `chapters/robust_RL.tex:88–98` (display `eq:mdp-value-Q`), with the robust value and
Q-function of `:76–84` and stationary randomized policies (`prelim.tex:66`).

Let `U` be an `(s,a)`-rectangular row family whose rows attain their infima, `V⋆ = optFix U M`
the robust optimality fixed point, `π⋆ = detPolicy (optPolicy U M)` and `K⋆` a worst-case
kernel for `V⋆`. Then

* `Q^{π,K}(s,a) = r(s,a) + γ ⟨K_{sa}, V^{π,K}⟩` for every kernel (ordinary Q consistency);
* `V⋆` is a supersolution of the ordinary Bellman inequality in the MDP with kernel `K⋆`, so
  `V^{π,K⋆} ≤ V⋆` for every stationary `π`, hence `Q^{π,σ}(s,a) ≤ Q^{π,K⋆}(s,a) ≤ robustQ V⋆ s a`;
* `Q^{π⋆,σ}(s,a) = robustQ V⋆ s a`, because `V^{π⋆,K} ≥ V^{π⋆,σ} = V⋆` for admissible `K`.

The adversary is static (one kernel for the whole trajectory), as in the book (`:78`).
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Ordinary Q consistency in the MDP with kernel `K`:
`Q^{π,K}(s,a) = r(s,a) + γ ⟨K_{sa}, V^{π,K}⟩`, for actual trajectory values. -/
theorem trajectoryExpectedQ_withKernel (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (π : StationaryPolicy State Action)
    (s : State) (a : Action) :
    (withKernel M K).trajectoryExpectedQ π s a =
      M.reward s a + M.discount * (K s a).expectation
        ((withKernel M K).trajectoryExpectedValue π) := by
  rw [DiscountedMDP.trajectoryExpectedQ_eq_policyFixedPoint,
    DiscountedMDP.policyFixedPoint_eq_reward_add_value,
    DiscountedMDP.trajectoryExpectedValue_eq_valueFixedPoint]
  rfl

/-- The worst-case kernel of a singleton row family is the kernel itself. -/
theorem worstKernel_singleton (K : State → Action → FiniteDistribution State)
    (h : ∀ s a, RowAttains ({K s a} : Set (FiniteDistribution State))) (V : State → ℝ) :
    worstKernel (fun s a ↦ ({K s a} : Set (FiniteDistribution State))) h V = K := by
  funext s a
  exact Set.mem_singleton_iff.mp (worstKernel_mem _ h V s a)

/-- A supersolution of the ordinary Bellman inequality in the MDP with kernel `K` bounds the
actual trajectory value of every stationary randomized policy from above. -/
theorem trajectoryExpectedValue_withKernel_le_of_super (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (π : StationaryPolicy State Action)
    {W : State → ℝ} (hW : ∀ x a, M.reward x a + M.discount * (K x a).expectation W ≤ W x)
    (s : State) : (withKernel M K).trajectoryExpectedValue π s ≤ W s := by
  haveI := M.state_nonempty
  set U1 : RowFamily State Action := fun x a ↦ ({K x a} : Set (FiniteDistribution State))
  have hU1 : ∀ x a, RowAttains (U1 x a) := fun x a ↦ rowAttains_singleton (K x a)
  have hval := (familyRobustValue_eq_policyFix U1 hU1 M π).2
  rw [worstKernel_singleton K hU1] at hval
  rw [hval]
  refine (policyOp_shiftBound U1 M π).ge_of_super M.discount_lt_one (policyFix_spec U1 M π)
    (fun x ↦ ?_) s
  unfold policyOp
  apply (π x).expectation_le_const
  intro a
  rw [rowInf_singleton]
  exact hW x a

/-- The optimal robust value is a supersolution of the ordinary Bellman inequality in the MDP
with its worst-case kernel. -/
theorem optFix_super_worstKernel (U : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (M : DiscountedMDP State Action) (x : State) (a : Action) :
    M.reward x a + M.discount *
        (worstKernel U hU (optFix U M) x a).expectation (optFix U M) ≤ optFix U M x := by
  letI : Nonempty Action := M.action_nonempty
  rw [← worstKernel_spec U hU (optFix U M) x a]
  change robustQ U M (optFix U M) x a ≤ optFix U M x
  conv_rhs => rw [← optFix_spec U M]
  exact le_actionMaximum (robustQ U M (optFix U M) x) a

theorem robustPolicyQ_bddBelow (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    BddBelow {v | ∃ K, RobustAdmissible ball M σ K ∧
      v = (withKernel M K).trajectoryExpectedQ π s a} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨K, -, rfl⟩
  exact ((withKernel M K).trajectoryExpectedQ_bounds π s a).1

theorem robustPolicyValue_bddBelow (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (π : StationaryPolicy State Action) (s : State) :
    BddBelow {v | ∃ K, RobustAdmissible ball M σ K ∧
      v = (withKernel M K).trajectoryExpectedValue π s} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨K, -, rfl⟩
  exact ((withKernel M K).trajectoryExpectedValue_bounds π s).1

/-- Every stationary randomized policy has robust Q-value at most `robustQ V⋆`. -/
theorem robustPolicyQ_le_robustQ_optFix (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    robustPolicyQ ball M σ π s a ≤
      robustQ (ballFamily ball M σ) M (optFix (ballFamily ball M σ) M) s a := by
  set U := ballFamily ball M σ
  set V := optFix U M
  set Kw := worstKernel U hU V
  have hadm : RobustAdmissible ball M σ Kw := fun x b ↦ worstKernel_mem U hU V x b
  calc robustPolicyQ ball M σ π s a ≤ (withKernel M Kw).trajectoryExpectedQ π s a :=
        csInf_le (robustPolicyQ_bddBelow ball M σ π s a) ⟨Kw, hadm, rfl⟩
    _ = M.reward s a + M.discount * (Kw s a).expectation
          ((withKernel M Kw).trajectoryExpectedValue π) := trajectoryExpectedQ_withKernel M Kw π s a
    _ ≤ M.reward s a + M.discount * (Kw s a).expectation V := by
        have hle : ∀ x, (withKernel M Kw).trajectoryExpectedValue π x ≤ V x :=
          trajectoryExpectedValue_withKernel_le_of_super M Kw π (optFix_super_worstKernel U hU M)
        have := (Kw s a).expectation_mono hle
        nlinarith [M.discount_nonneg]
    _ = robustQ U M V s a := by
        unfold robustQ
        rw [worstKernel_spec U hU V s a]

/-- The robust Q-value of the deterministic robust-optimal policy is `robustQ V⋆`. -/
theorem robustPolicyQ_optPolicy (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ)) (s : State) (a : Action) :
    robustPolicyQ ball M σ (detPolicy (optPolicy (ballFamily ball M σ) M)) s a =
      robustQ (ballFamily ball M σ) M (optFix (ballFamily ball M σ) M) s a := by
  set U := ballFamily ball M σ
  set V := optFix U M
  set πs := detPolicy (optPolicy U M)
  apply le_antisymm (robustPolicyQ_le_robustQ_optFix ball M σ hU πs s a)
  have hrob : robustPolicyValue ball M σ πs = V := by
    rw [robustPolicyValue_eq_policyFix ball M σ hU, policyFix_optPolicy]
  have hne : {v | ∃ K, RobustAdmissible ball M σ K ∧
      v = (withKernel M K).trajectoryExpectedQ πs s a}.Nonempty :=
    ⟨_, worstKernel U hU V, fun x b ↦ worstKernel_mem U hU V x b, rfl⟩
  apply le_csInf hne
  rintro _ ⟨K, hK, rfl⟩
  rw [trajectoryExpectedQ_withKernel M K πs s a]
  have hge : ∀ x, V x ≤ (withKernel M K).trajectoryExpectedValue πs x := by
    intro x
    rw [← hrob]
    exact csInf_le (robustPolicyValue_bddBelow ball M σ πs x) ⟨K, hK, rfl⟩
  have h1 : (K s a).expectation V ≤ (K s a).expectation
      ((withKernel M K).trajectoryExpectedValue πs) := (K s a).expectation_mono hge
  have h2 : rowInf (U s a) V ≤ (K s a).expectation V := rowInf_le (hK s a) V
  unfold robustQ
  nlinarith [M.discount_nonneg]

/-- Robust Q consistency for every stationary randomized policy (semantic anchor for
`robustPolicyQ`): `Q^{π,σ}(s,a) = r(s,a) + γ inf_{q ∈ U^σ(P^0_{s,a})} ⟨q, V^{π,σ}⟩`
(display `eq:bellman-equ-pi-infinite`, `robust_RL.tex:104–113`), the infimum over kernels being
attained by the worst-case kernel of
`V^{π,σ}`. -/
theorem robustPolicyQ_eq_reward_add_rowInf (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    robustPolicyQ ball M σ π s a = M.reward s a + M.discount *
      rowInf (ball (M.transition s a) σ) (robustPolicyValue ball M σ π) := by
  set U := ballFamily ball M σ
  set F := policyFix U M π
  set Kw := worstKernel U hU F
  have hrob : robustPolicyValue ball M σ π = F := robustPolicyValue_eq_policyFix ball M σ hU π
  have hKw : (withKernel M Kw).trajectoryExpectedValue π = F :=
    (familyRobustValue_eq_policyFix U hU M π).2
  rw [hrob]
  apply le_antisymm
  · calc robustPolicyQ ball M σ π s a ≤ (withKernel M Kw).trajectoryExpectedQ π s a :=
          csInf_le (robustPolicyQ_bddBelow ball M σ π s a)
            ⟨Kw, fun x b ↦ worstKernel_mem U hU F x b, rfl⟩
      _ = M.reward s a + M.discount * (Kw s a).expectation F := by
          rw [trajectoryExpectedQ_withKernel, hKw]
      _ = _ := by rw [← worstKernel_spec U hU F s a]; rfl
  · apply le_csInf (⟨_, Kw, fun x b ↦ worstKernel_mem U hU F x b, rfl⟩ :
      {v | ∃ K, RobustAdmissible ball M σ K ∧
        v = (withKernel M K).trajectoryExpectedQ π s a}.Nonempty)
    rintro _ ⟨K, hK, rfl⟩
    rw [trajectoryExpectedQ_withKernel M K π s a]
    have hge : ∀ x, F x ≤ (withKernel M K).trajectoryExpectedValue π x := by
      intro x
      rw [← hrob]
      exact csInf_le (robustPolicyValue_bddBelow ball M σ π x) ⟨K, hK, rfl⟩
    have h1 := (K s a).expectation_mono hge
    have h2 : rowInf (ball (M.transition s a) σ) F ≤ (K s a).expectation F :=
      rowInf_le (hK s a) F
    nlinarith [M.discount_nonneg]

/-- `eq:mdp-value-Q` for a ball family whose rows attain their infima: the deterministic
stationary policy `optPolicy` maximizes the robust value at every state and the robust
Q-function at every state-action pair, over stationary randomized policies. -/
theorem exists_det_robust_value_Q_optimal (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ)) :
    ∃ f : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue ball M σ π s ≤ robustPolicyValue ball M σ (detPolicy f) s) ∧
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ ball M σ π s a ≤ robustPolicyQ ball M σ (detPolicy f) s a) := by
  refine ⟨optPolicy (ballFamily ball M σ) M, fun π s ↦ ?_, fun π s a ↦ ?_⟩
  · rw [robustPolicyValue_eq_policyFix ball M σ hU, robustPolicyValue_eq_policyFix ball M σ hU,
      policyFix_optPolicy]
    exact policyFix_le_optFix _ M π s
  · rw [robustPolicyQ_optPolicy ball M σ hU]
    exact robustPolicyQ_le_robustQ_optFix ball M σ hU π s a

/-- `eq:mdp-value-Q`, TV ball, `σ ≥ 0`. -/
theorem exists_det_robust_value_Q_optimal_tv (M : DiscountedMDP State Action) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ∃ f : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue tvBall M σ π s ≤ robustPolicyValue tvBall M σ (detPolicy f) s) ∧
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ tvBall M σ π s a ≤ robustPolicyQ tvBall M σ (detPolicy f) s a) :=
  exists_det_robust_value_Q_optimal tvBall M σ (tvBall_family_rowAttains M hσ)

/-- `eq:mdp-value-Q`, χ² ball, `σ ≥ 0`. -/
theorem exists_det_robust_value_Q_optimal_chi (M : DiscountedMDP State Action) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ∃ f : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue chiBall M σ π s ≤ robustPolicyValue chiBall M σ (detPolicy f) s) ∧
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ chiBall M σ π s a ≤ robustPolicyQ chiBall M σ (detPolicy f) s a) :=
  exists_det_robust_value_Q_optimal chiBall M σ (chiBall_family_rowAttains M hσ)

end StatisticalRL.RobustRL.DRVI
