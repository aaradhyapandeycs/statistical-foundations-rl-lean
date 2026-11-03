import Formalization.ModelFree.QLearningStabilityInfinityNorm
import Formalization.ModelFree.QLearningComparatorConditionalCloseness
import Formalization.ModelFree.QLearningConditionalUniversalConstants

/-! Source Q-learning accuracy from actual stopped-law stability and comparator reductions. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
universe u v

/-- The actual stopped-prefix stability theorem gives the uniform optimal-Q
distance required by the selected-model comparator reduction. This has the
same candidate-to-nominal χ² ball orientation as the source and does not
assume a target-shaped closeness conclusion. -/
theorem qSource_actual_model_stability_from_stopped_law
    {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
    (M M' : DiscountedMDP State Action) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (hballs : ∀ s a, M'.transition s a ∈ qChiBall (M.transition s a) ρ) :
    ‖M'.trajectoryExpectedQ M'.optimalGreedyPolicy -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      Real.sqrt (M.discount * ρ / (2 * (1 - M.discount) ^ 3)) := by
  rw [mul_comm M.discount ρ]
  exact qChiBall_optimal_trajectoryQ_norm_stability M M' hr hγ ρ hρ hballs

/-- At any nonnegative source radius, the actual stopped-law result supplies
the positive-case selected-model stability input. The published comparator
reduction handles both zero endpoints and retains the exact additive source
shift `2ρ/(1−γ)^2`. -/
theorem qSource_robust_comparator_closeness_from_stopped_law
    {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ (hρ' : 0 ≤ ρ) s a,
      |qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ' s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
          Real.sqrt (M.discount * ρ / (2 * (1 - M.discount) ^ 3)) +
            2 * ρ / (1 - M.discount) ^ 2 ∧
      |qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ' s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
          Real.sqrt (M.discount * ρ / (2 * (1 - M.discount) ^ 3)) +
            2 * ρ / (1 - M.discount) ^ 2 := by
  have hbase := qComparator_closeness_of_positive_actualModel_stability M ρ hρ
    (by
      intro hγpos hρpos M' hr hγ hballs
      exact qSource_actual_model_stability_from_stopped_law M M' ρ
        (le_of_lt hρpos) hr hγ hballs)
  intro hρ' s a
  have hproof : hρ' = hρ := Subsingleton.elim _ _
  subst hρ'
  exact hbase s a

/-- Source `thm:infinite-horizon-simple` with its comparator-closeness
obligation discharged by the actual stopped-law stability theorem and the
published selected-model reduction. Constants are chosen before all problem
data. The event is under the actual synchronous product sampling law and
simultaneously covers every state-action pair. -/
theorem qLearning_exists_universal_constants_source_accuracy :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 < c₃ ∧
    ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      qSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (Q₀ : State → Action → ℝ),
      (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ) ^ 4 * Real.log
        ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) /
          ((1 - M.discount) ^ 4 * ε ^ 2) ≤ T →
      1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
        |qSampledIterate M η T Q₀ data s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε} := by
  obtain ⟨c₁, c₂, c₃, hc₂, hc₂₁, hc₁, hc₃, hconditional⟩ :=
    qLearning_exists_universal_constants_conditional
  refine ⟨c₁, c₂, c₃, hc₂, hc₂₁, hc₁, hc₃, ?_⟩
  intro State Action instState instAction M η δ ε T hγhalf hA hT hδ hδ1
    hε hεmax hs Q₀ h₀ hbudget
  let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
    (Fintype.card State) (Fintype.card Action) T
  have hρ : 0 ≤ ρ := by
    have hηbar := qChiSourceRateEnvelope_pos M.discount c₂ T
      M.discount_lt_one hc₂ hT
    exact (qChiSourceRadius_pos _ δ _ _ T hηbar hδ hδ1
      (Fintype.card_pos_iff.mpr M.state_nonempty)
      (Fintype.card_pos_iff.mpr M.action_nonempty) hT).le
  have hclose :
      (∀ (hρ' : 0 ≤ ρ) s a,
        |qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ' s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
            Real.sqrt (M.discount * ρ / (2 * (1 - M.discount) ^ 3)) +
              2 * ρ / (1 - M.discount) ^ 2 ∧
        |qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ' s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
            Real.sqrt (M.discount * ρ / (2 * (1 - M.discount) ^ 3)) +
              2 * ρ / (1 - M.discount) ^ 2) :=
    qSource_robust_comparator_closeness_from_stopped_law M ρ hρ
  exact hconditional State Action M η δ ε T hγhalf hA hT
    hδ hδ1 hε hεmax hs Q₀ h₀ hbudget hclose

end StatisticalRL.QLearning
