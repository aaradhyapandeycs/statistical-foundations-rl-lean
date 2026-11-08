import Formalization.RobustRL.DRVI.PolicyEvaluation

/-!
# Robust optimality and a deterministic optimal policy (milestone 1, R0d)

Source: `chapters/robust_RL.tex:88–101` (`V^{⋆,σ} = max_π V^{π,σ}`; existence of a
deterministic optimal policy, cited at `:90`), `:103–117` (robust Bellman optimality),
`:118–133` (operator `T^σ`, unique fixed point and γ-contraction, cited).

For a row family whose rows attain their infima, the robust optimality operator
`T V(s) = max_a [r(s,a) + γ inf_{q ∈ U s a} ⟨q, V⟩]` has a unique fixed point `optFix`; a
greedy deterministic policy `optPolicy` for `optFix` has robust value `optFix`, every stationary
randomized policy has robust value `≤ optFix`, hence `robustOptimalValue = optFix` and the
supremum is attained by the deterministic stationary policy `optPolicy` at every state at once.
-/

open scoped BigOperators NNReal

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The robust action value `r(s,a) + γ inf_{q ∈ U s a} ⟨q, V⟩`. -/
noncomputable def robustQ (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (V : State → ℝ) (s : State) (a : Action) : ℝ :=
  M.reward s a + M.discount * rowInf (U s a) V

/-- Robust optimality operator `T V(s) = max_a robustQ V s a`. -/
noncomputable def optOp (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (V : State → ℝ) (s : State) : ℝ :=
  letI : Nonempty Action := M.action_nonempty
  actionMaximum (robustQ U M V s)

theorem robustQ_shift (U : RowFamily State Action) (M : DiscountedMDP State Action)
    {V W : State → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, V x ≤ W x + c) (s : State) (a : Action) :
    robustQ U M V s a ≤ robustQ U M W s a + M.discount * c := by
  unfold robustQ
  have : rowInf (U s a) V ≤ rowInf (U s a) W + c := by
    rcases (U s a).eq_empty_or_nonempty with hE | hU
    · simp [rowInf, hE, hc]
    · exact rowInf_le_add hU h
  nlinarith [M.discount_nonneg]

theorem optOp_shiftBound (U : RowFamily State Action) (M : DiscountedMDP State Action) :
    ShiftBound M.discount (optOp U M) := by
  letI : Nonempty Action := M.action_nonempty
  intro V W c hc h s
  unfold optOp
  apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
  intro a _
  have h1 := robustQ_shift U M hc h s a
  have h2 := le_actionMaximum (robustQ U M W s) a
  linarith

/-- The unique fixed point of the robust optimality operator. -/
noncomputable def optFix (U : RowFamily State Action) (M : DiscountedMDP State Action) :
    State → ℝ :=
  Classical.choose ((optOp_shiftBound U M).exists_unique M.discount_nonneg M.discount_lt_one)

theorem optFix_spec (U : RowFamily State Action) (M : DiscountedMDP State Action) :
    optOp U M (optFix U M) = optFix U M :=
  (Classical.choose_spec ((optOp_shiftBound U M).exists_unique M.discount_nonneg
    M.discount_lt_one)).1

theorem eq_optFix (U : RowFamily State Action) (M : DiscountedMDP State Action)
    {V : State → ℝ} (hV : optOp U M V = V) : V = optFix U M :=
  (Classical.choose_spec ((optOp_shiftBound U M).exists_unique M.discount_nonneg
    M.discount_lt_one)).2 V hV

theorem policyOp_eq_expectation_robustQ (U : RowFamily State Action)
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (V : State → ℝ)
    (s : State) : policyOp U M π V s = (π s).expectation (robustQ U M V s) := rfl

theorem policyOp_le_optOp (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) (s : State) :
    policyOp U M π V s ≤ optOp U M V s := by
  letI : Nonempty Action := M.action_nonempty
  rw [policyOp_eq_expectation_robustQ]
  exact (π s).expectation_le_const (fun a ↦ le_actionMaximum _ a)

/-- A greedy action for `robustQ V` at `s`. -/
noncomputable def greedyAction (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (V : State → ℝ) (s : State) : Action :=
  letI : Nonempty Action := M.action_nonempty
  Classical.choose (Finset.exists_max_image Finset.univ (robustQ U M V s) Finset.univ_nonempty)

theorem greedyAction_spec (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (V : State → ℝ) (s : State) (a : Action) :
    robustQ U M V s a ≤ robustQ U M V s (greedyAction U M V s) := by
  letI : Nonempty Action := M.action_nonempty
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ (robustQ U M V s)
    Finset.univ_nonempty)).2 a (Finset.mem_univ a)

theorem optOp_eq_greedy (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (V : State → ℝ) (s : State) :
    optOp U M V s = robustQ U M V s (greedyAction U M V s) := by
  letI : Nonempty Action := M.action_nonempty
  apply le_antisymm
  · exact (Finset.sup'_le_iff Finset.univ_nonempty _).2
      (fun a _ ↦ greedyAction_spec U M V s a)
  · exact le_actionMaximum _ _

/-- Any selector maximizing `robustQ V` realizes the optimality operator. -/
theorem policyOp_detPolicy_eq_optOp (U : RowFamily State Action)
    (M : DiscountedMDP State Action) (V : State → ℝ) {f : State → Action}
    (hf : ∀ s a, robustQ U M V s a ≤ robustQ U M V s (f s)) :
    policyOp U M (detPolicy f) V = optOp U M V := by
  letI : Nonempty Action := M.action_nonempty
  funext s
  rw [policyOp_detPolicy]
  apply le_antisymm
  · exact le_actionMaximum (robustQ U M V s) (f s)
  · exact (Finset.sup'_le_iff Finset.univ_nonempty _).2 (fun a _ ↦ hf s a)

/-- The deterministic stationary robust-optimal policy `π⋆`, greedy for `optFix`. -/
noncomputable def optPolicy (U : RowFamily State Action) (M : DiscountedMDP State Action) :
    State → Action :=
  greedyAction U M (optFix U M)

/-- Every greedy selector of `optFix` is optimal. -/
theorem policyFix_greedy (U : RowFamily State Action) (M : DiscountedMDP State Action)
    {f : State → Action} (hf : ∀ s a, robustQ U M (optFix U M) s a ≤
      robustQ U M (optFix U M) s (f s)) :
    policyFix U M (detPolicy f) = optFix U M := by
  symm
  apply eq_policyFix
  rw [policyOp_detPolicy_eq_optOp U M _ hf]
  exact optFix_spec U M

theorem policyFix_optPolicy (U : RowFamily State Action) (M : DiscountedMDP State Action) :
    policyFix U M (detPolicy (optPolicy U M)) = optFix U M := by
  exact policyFix_greedy U M (greedyAction_spec U M _)

theorem policyFix_le_optFix (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : policyFix U M π s ≤ optFix U M s := by
  haveI := M.state_nonempty
  refine (optOp_shiftBound U M).le_of_sub M.discount_lt_one (optFix_spec U M) (fun t ↦ ?_) s
  calc policyFix U M π t = policyOp U M π (policyFix U M π) t := by
        rw [policyFix_spec]
    _ ≤ optOp U M (policyFix U M π) t := policyOp_le_optOp U M π _ t

theorem optFix_bounds (U : RowFamily State Action) (hU : ∀ s a, (U s a).Nonempty)
    (M : DiscountedMDP State Action) (s : State) :
    0 ≤ optFix U M s ∧ optFix U M s ≤ 1 / (1 - M.discount) := by
  rw [← policyFix_optPolicy U M]
  exact policyFix_bounds U hU M _ s

/-- Generic R0d: the optimal robust value over stationary randomized policies equals
`optFix` and is attained by the deterministic policy `optPolicy`. -/
theorem familyOptimal_eq_optFix (U : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (M : DiscountedMDP State Action) (s : State) :
    sSup (Set.range fun π : StationaryPolicy State Action ↦ familyRobustValue U M π s) =
      optFix U M s := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨detPolicy (optPolicy U M), ?_⟩
    simp only
    rw [(familyRobustValue_eq_policyFix U hU M _).1, policyFix_optPolicy]
  · rintro _ ⟨π, rfl⟩
    simp only
    rw [(familyRobustValue_eq_policyFix U hU M π).1]
    exact policyFix_le_optFix U M π s

/-- R0d for ball families: `V^{⋆,σ} = optFix`. -/
theorem robustOptimalValue_eq_optFix (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ)) :
    robustOptimalValue ball M σ = optFix (ballFamily ball M σ) M := by
  funext s
  exact familyOptimal_eq_optFix (ballFamily ball M σ) hU M s

/-- A deterministic stationary policy attains `V^{⋆,σ}` at every state simultaneously. -/
theorem robustOptimalValue_eq_robustPolicyValue_optPolicy (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ)) :
    robustOptimalValue ball M σ =
      robustPolicyValue ball M σ (detPolicy (optPolicy (ballFamily ball M σ) M)) := by
  rw [robustOptimalValue_eq_optFix ball M σ hU, robustPolicyValue_eq_policyFix ball M σ hU,
    policyFix_optPolicy]

theorem tvBall_family_rowAttains (M : DiscountedMDP State Action) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ s a, RowAttains (tvBall (M.transition s a) σ) :=
  fun _ _ ↦ tvBall_rowAttains _ hσ

theorem chiBall_family_rowAttains (M : DiscountedMDP State Action) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ s a, RowAttains (chiBall (M.transition s a) σ) :=
  fun _ _ ↦ chiBall_rowAttains _ hσ

end StatisticalRL.RobustRL.DRVI
