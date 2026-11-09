import Formalization.ModelFree.QLearningSamplingDefinitions

/-! pathwise comparison of the auxiliary policy iteration with Q-learning. -/

namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Pathwise `Q̃_t ≤ Q_t` (`chapters/generative_model_model_free.tex:1871`): with the same
samples and initialization, following `f` never exceeds maximizing over actions, as long
as the rates used through `t` lie in `[0,1]`. -/
theorem qPolicyEvaluationIterate_le_qLearningIterate (M : DiscountedMDP State Action)
    (f : State → Action) (η : ℕ → ℝ) (samples : ℕ → State → Action → State)
    (Q₀ : State → Action → ℝ) (t : ℕ) (hη : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1)
    (s : State) (a : Action) :
    qPolicyEvaluationIterate M f η samples Q₀ t s a ≤
      qLearningIterate M η samples Q₀ t s a := by
  induction t generalizing s a with
  | zero => exact le_rfl
  | succ t ih =>
    have he := hη (t + 1) (by omega) le_rfl
    have hp : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
      fun k hk ht ↦ hη k hk (Nat.le_trans ht (Nat.le_succ t))
    set s' := samples (t + 1) s a
    have hcur := ih hp s a
    have hnext : qPolicyEvaluationIterate M f η samples Q₀ t s' (f s') ≤
        qLearningValue M (qLearningIterate M η samples Q₀ t) s' := by
      letI : Nonempty Action := M.action_nonempty
      exact (ih hp s' (f s')).trans
        (le_actionMaximum (qLearningIterate M η samples Q₀ t s') (f s'))
    change (1 - η (t + 1)) * qPolicyEvaluationIterate M f η samples Q₀ t s a +
        η (t + 1) * (M.reward s a + M.discount *
          qPolicyEvaluationIterate M f η samples Q₀ t s' (f s')) ≤
      (1 - η (t + 1)) * qLearningIterate M η samples Q₀ t s a +
        η (t + 1) * (M.reward s a + M.discount *
          qLearningValue M (qLearningIterate M η samples Q₀ t) s')
    have h1 := mul_le_mul_of_nonneg_left hcur (sub_nonneg.mpr he.2)
    have h2 := mul_le_mul_of_nonneg_left hnext M.discount_nonneg
    have h3 := mul_le_mul_of_nonneg_left (add_le_add_left h2 (M.reward s a)) he.1
    linarith

/-- The auxiliary iteration stays nonnegative from a nonnegative initialization. -/
theorem qPolicyEvaluationIterate_nonneg (M : DiscountedMDP State Action)
    (f : State → Action) (η : ℕ → ℝ) (samples : ℕ → State → Action → State)
    (Q₀ : State → Action → ℝ) (h₀ : ∀ s a, 0 ≤ Q₀ s a) (t : ℕ)
    (hη : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1) (s : State) (a : Action) :
    0 ≤ qPolicyEvaluationIterate M f η samples Q₀ t s a := by
  induction t generalizing s a with
  | zero => exact h₀ s a
  | succ t ih =>
    have he := hη (t + 1) (by omega) le_rfl
    have hp : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
      fun k hk ht ↦ hη k hk (Nat.le_trans ht (Nat.le_succ t))
    set s' := samples (t + 1) s a
    change 0 ≤ (1 - η (t + 1)) * qPolicyEvaluationIterate M f η samples Q₀ t s a +
        η (t + 1) * (M.reward s a + M.discount *
          qPolicyEvaluationIterate M f η samples Q₀ t s' (f s'))
    have h1 := mul_nonneg (sub_nonneg.mpr he.2) (ih hp s a)
    have h2 := mul_nonneg he.1 (add_nonneg (M.reward_nonneg s a)
      (mul_nonneg M.discount_nonneg (ih hp s' (f s'))))
    linarith

end StatisticalRL.QLearning
