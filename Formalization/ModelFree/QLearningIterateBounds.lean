import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.FixedPoint

/-! Source synchronous Q-learning and deterministic boundedness. -/
namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Value obtained by maximizing the entire current Q array at each state. -/
noncomputable def qLearningValue (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) : State → ℝ := by
  letI : Nonempty Action := M.action_nonempty
  exact fun s ↦ actionMaximum (Q s)

/-- Synchronous update: every (s,a) uses Q_t and its own next-state draw at
time t+1. The array is not updated sequentially within an iteration. -/
noncomputable def qLearningIterate (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State)
    (Q₀ : State → Action → ℝ) : ℕ → State → Action → ℝ
  | 0 => Q₀
  | t + 1 => fun s a ↦
      (1 - η (t + 1)) * qLearningIterate M η samples Q₀ t s a +
        η (t + 1) * (M.reward s a + M.discount *
          qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t + 1) s a))

/-- Maximizing an array in the return interval preserves that interval. -/
theorem qLearningValue_bounds (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ)
    (hQ : ∀ s a, 0 ≤ Q s a ∧ Q s a ≤ M.effectiveHorizon) (s : State) :
    0 ≤ qLearningValue M Q s ∧ qLearningValue M Q s ≤ M.effectiveHorizon := by
  letI : Nonempty Action := M.action_nonempty
  change 0 ≤ actionMaximum (Q s) ∧ actionMaximum (Q s) ≤ M.effectiveHorizon
  constructor
  · exact (hQ s (Classical.choice M.action_nonempty)).1.trans
      (le_actionMaximum (Q s) (Classical.choice M.action_nonempty))
  · exact (Finset.sup'_le_iff Finset.univ_nonempty (Q s)).2 (fun a _ ↦ (hQ s a).2)

/-- Source Lemma `lemma:non-negativity-Qt-Vt`, pathwise Q part: only rates
used through t must lie in [0,1]. No sampling or independence is assumed. -/
theorem qLearningIterate_bounds (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1)
    (s : State) (a : Action) :
    0 ≤ qLearningIterate M η samples Q₀ t s a ∧
      qLearningIterate M η samples Q₀ t s a ≤ M.effectiveHorizon := by
  induction t generalizing s a with
  | zero => exact h₀ s a
  | succ t ih =>
    have he := hη (t + 1) (by omega) (le_refl _)
    have hp : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
      fun k hk ht ↦ hη k hk (Nat.le_trans ht (Nat.le_succ t))
    have hs := ih hp s a
    have hv := qLearningValue_bounds M (qLearningIterate M η samples Q₀ t)
      (fun x b ↦ ih hp x b) (samples (t + 1) s a)
    have htarget₀ : 0 ≤ M.reward s a + M.discount *
        qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t + 1) s a) :=
      add_nonneg (M.reward_nonneg s a) (mul_nonneg M.discount_nonneg hv.1)
    have htarget₁ : M.reward s a + M.discount *
        qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t + 1) s a) ≤ M.effectiveHorizon := by
      calc
        _ ≤ 1 + M.discount * M.effectiveHorizon :=
          add_le_add (M.reward_le_one s a) (mul_le_mul_of_nonneg_left hv.2 M.discount_nonneg)
        _ = M.effectiveHorizon := M.effectiveHorizon_recursion
    change 0 ≤ (1 - η (t + 1)) * qLearningIterate M η samples Q₀ t s a +
      η (t + 1) * (M.reward s a + M.discount *
        qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t + 1) s a)) ∧ _
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr he.2) hs.1) (mul_nonneg he.1 htarget₀)
    · change (1 - η (t + 1)) * qLearningIterate M η samples Q₀ t s a +
        η (t + 1) * (M.reward s a + M.discount *
          qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t + 1) s a)) ≤ M.effectiveHorizon
      nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (sub_nonneg.mpr hs.2),
        mul_nonneg he.1 (sub_nonneg.mpr htarget₁)]

/-- The corresponding value estimate has the same pathwise bounds. -/
theorem qLearningIterate_value_bounds (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1) (s : State) :
    0 ≤ qLearningValue M (qLearningIterate M η samples Q₀ t) s ∧
      qLearningValue M (qLearningIterate M η samples Q₀ t) s ≤ M.effectiveHorizon :=
  qLearningValue_bounds M _ (fun x a ↦ qLearningIterate_bounds M η samples Q₀ h₀ t hη x a) s

/-- The error is measured against actual optimal-greedy trajectory Q. -/
theorem qLearningIterate_optimalQ_error_norm_le (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1) :
    ‖qLearningIterate M η samples Q₀ t - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      M.effectiveHorizon := by
  apply (pi_norm_le_iff_of_nonneg M.effectiveHorizon_nonneg).2
  intro s
  apply (pi_norm_le_iff_of_nonneg M.effectiveHorizon_nonneg).2
  intro a
  have hi := qLearningIterate_bounds M η samples Q₀ h₀ t hη s a
  have ho := M.optimalityFixedPoint_bounds s a
  rw [← M.optimalGreedy_trajectoryQ s a] at ho
  change |qLearningIterate M η samples Q₀ t s a -
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ M.effectiveHorizon
  apply abs_le.mpr
  constructor <;> dsimp [DiscountedMDP.effectiveHorizon] at * <;> linarith

end StatisticalRL.QLearning
