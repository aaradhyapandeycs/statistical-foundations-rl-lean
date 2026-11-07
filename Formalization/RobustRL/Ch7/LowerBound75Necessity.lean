import Formalization.RobustRL.Ch7.LowerBound75

/-!
# Corrected Theorem 7.5: necessity of the added hypotheses

* `printed_at_fails`: the printed body is false at `A = 1` for every `c₃, c₄ > 0`.
* `knownReward_needs_two_actions`: the known-reward form without `A ≥ 2` is false.
* `knownReward_needs_two_states`: the known-reward form without `S ≥ 2` is false.

All three are adapted from the independent review probes
(`singleton_action_fails`, `kr_one_state_fails`).
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound75

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage
  StatisticalRL.RobustRL.Ch7.LowerBound73

local instance lowerBound75NecStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- The known-reward form (`Thm7_5_corrected_knownReward_at`) with the hypothesis `S ≥ 2`
dropped (only `A ≥ 2` added to the printed body). Refuted by `knownReward_needs_two_states`. -/
def Thm7_5_knownReward_noTwoStates_at (c₃ c₄ : ℝ) : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    2 ≤ Fintype.card Action →
    3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
    (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
              robustPolicyValueAt chiBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
              robustPolicyValueAt chiBall M₁ σ (est data) μ})

/-- The known-reward form with the hypothesis `A ≥ 2` dropped (only `S ≥ 2` added). Refuted by
`knownReward_needs_two_actions`. -/
def Thm7_5_knownReward_noTwoActions_at (c₃ c₄ : ℝ) : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    2 ≤ Fintype.card State →
    3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
    (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
              robustPolicyValueAt chiBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
              robustPolicyValueAt chiBall M₁ σ (est data) μ})

section OneState

-- adapted from the independent review probe 
variable {State Action : Type*} [Fintype State] [Fintype Action] [Subsingleton State]

theorem val_single (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (π : StationaryPolicy State Action) (s : State) :
    robustPolicyValue chiBall M σ π s =
      (π s).expectation (M.reward s) / (1 - M.discount) := by
  have h1γ : (1 - M.discount) ≠ 0 := by linarith [M.discount_lt_one]
  set c := (π s).expectation (M.reward s) / (1 - M.discount) with hc
  set W : State → ℝ := fun _ ↦ c with hW
  have hval : ∀ K : State → Action → FiniteDistribution State,
      (withKernel M K).trajectoryExpectedValue π s = c := by
    intro K
    have hfix : (withKernel M K).valueBellman π W = W := by
      funext t
      obtain rfl : t = s := Subsingleton.elim t s
      rw [LowerBound73.valueBellman_withKernel]
      have hfun : (fun a ↦ M.reward t a + M.discount * (K t a).expectation W) =
          fun a ↦ M.reward t a + M.discount * c := by
        funext a
        rw [LowerBound73.expectation_subsingleton _ _ t]
      rw [hfun, FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
      simp only [hW, hc]
      field_simp
      ring
    rw [(withKernel M K).trajectoryExpectedValue_eq_valueFixedPoint,
      ← ((withKernel M K).valueFixedPoint_characterization π W).mp hfix]
  have hset : {v | ∃ K, RobustAdmissible chiBall M σ K ∧
      v = (withKernel M K).trajectoryExpectedValue π s} = {c} := by
    ext v
    constructor
    · rintro ⟨K, -, rfl⟩
      exact hval K
    · intro hv
      rw [Set.mem_singleton_iff.mp hv]
      exact ⟨M.transition, fun _ _ ↦ QLearning.qChiBall_self _ σ hσ0, (hval _).symm⟩
  unfold robustPolicyValue
  rw [hset, csInf_singleton]

theorem opt_le_det (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 ≤ σ) (s : State)
    (a : Action) (ha : ∀ b, M.reward s b ≤ M.reward s a) :
    robustOptimalValue chiBall M σ s ≤ robustPolicyValue chiBall M σ (detPolicy fun _ ↦ a) s := by
  have h1γ : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  unfold robustOptimalValue
  apply csSup_le (Set.range_nonempty_iff_nonempty.mpr ⟨detPolicy fun _ ↦ a⟩)
  rintro v ⟨π, rfl⟩
  show robustPolicyValue chiBall M σ π s ≤ _
  rw [val_single M hσ0, val_single M hσ0]
  apply div_le_div_of_nonneg_right _ h1γ.le
  have hd : (detPolicy (fun _ : State ↦ a) s).expectation (M.reward s) = M.reward s a := by
    simp [detPolicy]
  rw [hd]
  have := FiniteDistribution.expectation_mono (π s) ha
  rwa [FiniteDistribution.expectation_const] at this

end OneState

/-- **`S ≥ 2` is necessary under known rewards** (`State = Unit`, `Action = Fin 2`, `γ = 3/4`,
`σ = 1`, `ε = c₃/4`, `N = 0`; playing `argmax r` is robust-optimal). Adapted from the
independent review probe. -/
theorem knownReward_needs_two_states (c₃ c₄ : ℝ) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) :
    ¬ Thm7_5_knownReward_noTwoStates_at c₃ c₄ := by
  classical
  intro H
  obtain ⟨M₀, M₁, μ, -, -, hr, hall⟩ := H Unit (Fin 2) (3 / 4) 1 (c₃ / 4) 0
    (by simp) (by norm_num) (by norm_num) (by norm_num)
    (by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith)
    (by rw [Nat.cast_zero]; positivity)
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (M₀.reward ()) Finset.univ_nonempty
  have hgap : ∀ M : DiscountedMDP Unit (Fin 2), M.reward = M₀.reward →
      robustOptimalValueAt chiBall M 1 μ -
        robustPolicyValueAt chiBall M 1 (detPolicy fun _ ↦ a) μ ≤ 0 := by
    intro M hM
    have := FiniteDistribution.expectation_mono μ (fun s ↦ opt_le_det M
      (by norm_num : (0 : ℝ) ≤ 1) s a (fun b ↦ by
        obtain rfl : s = () := Subsingleton.elim _ _
        rw [hM]; exact ha b (Finset.mem_univ b)))
    unfold robustOptimalValueAt robustPolicyValueAt
    linarith
  have := hall (fun _ ↦ detPolicy fun _ ↦ a)
  have hemp : ∀ M : DiscountedMDP Unit (Fin 2), M.reward = M₀.reward →
      {data : ModelBasedPolicyLearning.Samples Unit (Fin 2) 0 | c₃ / 4 <
        robustOptimalValueAt chiBall M 1 μ -
          robustPolicyValueAt chiBall M 1 ((fun _ ↦ detPolicy fun _ ↦ a) data) μ} = ∅ := by
    intro M hM; ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have := hgap M hM
    linarith
  rw [hemp M₀ rfl, hemp M₁ hr.symm] at this
  simp at this
  norm_num at this


/-- **`A ≥ 2` is necessary** (printed body, `A = 1`: every policy is optimal). Adapted from the
independent review probe. -/
theorem printed_at_fails (c₃ c₄ : ℝ) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) :
    ¬ Thm7_5_printed_at c₃ c₄ := by
  intro H
  obtain ⟨M₀, M₁, μ, -, -, hall⟩ := H (Fin 2) Unit (3 / 4) 1 (c₃ / 4) 0
    (by norm_num) (by norm_num) (by norm_num) (by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith)
    (by rw [Nat.cast_zero]; positivity)
  have key : ∀ (M : DiscountedMDP (Fin 2) Unit) (π : StationaryPolicy (Fin 2) Unit),
      robustOptimalValueAt chiBall M 1 μ - robustPolicyValueAt chiBall M 1 π μ = 0 := by
    intro M π
    have hconst : ∀ π' : StationaryPolicy (Fin 2) Unit, π' = π := by
      intro π'; funext s
      apply HorizonTrap.fd_ext; intro u
      rw [(π' s).prob_eq_one_of_subsingleton u, (π s).prob_eq_one_of_subsingleton u]
    have hopt : ∀ s, robustOptimalValue chiBall M 1 s = robustPolicyValue chiBall M 1 π s := by
      intro s
      unfold robustOptimalValue
      have : (Set.range fun π' : StationaryPolicy (Fin 2) Unit ↦
          robustPolicyValue chiBall M 1 π' s) = {robustPolicyValue chiBall M 1 π s} := by
        ext v; constructor
        · rintro ⟨π', rfl⟩; rw [hconst π']; rfl
        · intro hv; exact ⟨π, (Set.mem_singleton_iff.mp hv).symm⟩
      rw [this, csSup_singleton]
    unfold robustOptimalValueAt robustPolicyValueAt
    rw [show robustOptimalValue chiBall M 1 = robustPolicyValue chiBall M 1 π from funext hopt, sub_self]
  have := hall (fun _ _ ↦ pointMass ())
  have hemp : ∀ M : DiscountedMDP (Fin 2) Unit, {data : ModelBasedPolicyLearning.Samples
      (Fin 2) Unit 0 | c₃ / 4 < robustOptimalValueAt chiBall M 1 μ -
        robustPolicyValueAt chiBall M 1 ((fun _ _ ↦ pointMass ()) data) μ} = ∅ := by
    intro M; ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [key M]; positivity
  rw [hemp M₀, hemp M₁] at this
  simp at this
  norm_num at this


/-- **`A ≥ 2` is necessary under known rewards** (`State = Fin 2`, `Action = Unit`). Adapted from
the independent review probe. -/
theorem knownReward_needs_two_actions (c₃ c₄ : ℝ) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄) :
    ¬ Thm7_5_knownReward_noTwoActions_at c₃ c₄ := by
  intro H
  obtain ⟨M₀, M₁, μ, -, -, -, hall⟩ := H (Fin 2) Unit (3 / 4) 1 (c₃ / 4) 0
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith)
    (by rw [Nat.cast_zero]; positivity)
  have key : ∀ (M : DiscountedMDP (Fin 2) Unit) (π : StationaryPolicy (Fin 2) Unit),
      robustOptimalValueAt chiBall M 1 μ - robustPolicyValueAt chiBall M 1 π μ = 0 := by
    intro M π
    have hconst : ∀ π' : StationaryPolicy (Fin 2) Unit, π' = π := by
      intro π'; funext s
      apply HorizonTrap.fd_ext; intro u
      rw [(π' s).prob_eq_one_of_subsingleton u, (π s).prob_eq_one_of_subsingleton u]
    have hopt : ∀ s, robustOptimalValue chiBall M 1 s = robustPolicyValue chiBall M 1 π s := by
      intro s
      unfold robustOptimalValue
      have : (Set.range fun π' : StationaryPolicy (Fin 2) Unit ↦
          robustPolicyValue chiBall M 1 π' s) = {robustPolicyValue chiBall M 1 π s} := by
        ext v; constructor
        · rintro ⟨π', rfl⟩; rw [hconst π']; rfl
        · intro hv; exact ⟨π, (Set.mem_singleton_iff.mp hv).symm⟩
      rw [this, csSup_singleton]
    unfold robustOptimalValueAt robustPolicyValueAt
    rw [show robustOptimalValue chiBall M 1 = robustPolicyValue chiBall M 1 π from funext hopt, sub_self]
  have := hall (fun _ _ ↦ pointMass ())
  have hemp : ∀ M : DiscountedMDP (Fin 2) Unit, {data : ModelBasedPolicyLearning.Samples
      (Fin 2) Unit 0 | c₃ / 4 < robustOptimalValueAt chiBall M 1 μ -
        robustPolicyValueAt chiBall M 1 ((fun _ _ ↦ pointMass ()) data) μ} = ∅ := by
    intro M; ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [key M]; positivity
  rw [hemp M₀, hemp M₁] at this
  simp at this
  norm_num at this

end StatisticalRL.RobustRL.Ch7.LowerBound75
