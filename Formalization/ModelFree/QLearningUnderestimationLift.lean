import Formalization.ModelFree.QLearningSamplingDefinitions
import Formalization.ModelFree.TDSourceSamplingDefinitions
import Formalization.MDP.FiniteOptimal

/-! the auxiliary policy iteration is TD learning on a lifted state-action chain.

The lifted MDP has states `State × Action`, a single action, reward `r(s,a)`, the same
discount, and transition from `(s,a)` to `(s', f s')` with `s' ∼ P(·|s,a)`. -/

namespace StatisticalRL.QLearning
open StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The law of `(s', f s')` for `s' ∼ P(·|s,a)`. -/
noncomputable def qPolicyLiftTransition (M : DiscountedMDP State Action) (f : State → Action)
    (s : State) (a : Action) : FiniteDistribution (State × Action) :=
  (M.transition s a).bind (fun s' ↦ EnvironmentStage.pointMass (s', f s'))

/-- The state-action chain induced by following `f` after the first action. -/
noncomputable def qPolicyLiftMDP (M : DiscountedMDP State Action) (f : State → Action) :
    DiscountedMDP (State × Action) Unit where
  state_nonempty := by
    haveI := M.state_nonempty
    haveI := M.action_nonempty
    infer_instance
  action_nonempty := ⟨()⟩
  transition x _ := qPolicyLiftTransition M f x.1 x.2
  reward x _ := M.reward x.1 x.2
  reward_nonneg x _ := M.reward_nonneg x.1 x.2
  reward_le_one x _ := M.reward_le_one x.1 x.2
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- The only policy on the single-action lifted chain. -/
noncomputable def qPolicyLiftPolicy : StationaryPolicy (State × Action) Unit :=
  fun _ ↦ EnvironmentStage.pointMass ()

/-- Lift a Q-learning sample path to the state-action chain. -/
def qPolicyLiftSamples (f : State → Action) (samples : ℕ → State → Action → State) :
    ℕ → State × Action → State × Action :=
  fun t x ↦ (samples t x.1 x.2, f (samples t x.1 x.2))

/-- Lift an exact-T Q-learning data array coordinatewise. -/
def qPolicyLiftData (f : State → Action) {T : ℕ} (data : QSamples State Action T) :
    TDSourceSamples (State × Action) T :=
  fun i ↦ (data i, f (data i))

theorem qPolicyLift_expectation (M : DiscountedMDP State Action) (f : State → Action)
    (s : State) (a : Action) (g : State × Action → ℝ) :
    (qPolicyLiftTransition M f s a).expectation g =
      (M.transition s a).expectation (fun s' ↦ g (s', f s')) := by
  unfold qPolicyLiftTransition
  rw [FiniteDistribution.expectation_bind]
  simp only [EnvironmentStage.expectation_pointMass]

theorem qPolicyLift_policyReward (M : DiscountedMDP State Action) (f : State → Action)
    (x : State × Action) :
    policyReward (qPolicyLiftMDP M f) qPolicyLiftPolicy x = M.reward x.1 x.2 := by
  unfold policyReward DiscountedMDP.policyExpectedReward qPolicyLiftPolicy
  rw [EnvironmentStage.expectation_pointMass]
  rfl

/-- Pathwise identity: TD on the lifted chain is the auxiliary policy iteration. -/
theorem tdIterate_qPolicyLift (M : DiscountedMDP State Action) (f : State → Action)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (t : ℕ) (x : State × Action) :
    tdIterate (qPolicyLiftMDP M f) qPolicyLiftPolicy η (qPolicyLiftSamples f samples)
        (fun y ↦ Q₀ y.1 y.2) t x =
      qPolicyEvaluationIterate M f η samples Q₀ t x.1 x.2 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [tdIterate, qPolicyEvaluationIterate]
    rw [qPolicyLift_policyReward, ih x, ih]
    rfl

/-- TD iterates agree up to `t` when the sample paths agree at times `1, …, t`. -/
theorem tdIterate_congr_samples {S A : Type*} [Fintype S] [Fintype A]
    (M : DiscountedMDP S A) (π : StationaryPolicy S A) (η : ℕ → ℝ)
    (samples₁ samples₂ : ℕ → S → S) (V₀ : S → ℝ) (t : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ t → samples₁ k = samples₂ k) :
    tdIterate M π η samples₁ V₀ t = tdIterate M π η samples₂ V₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun k hk hkt ↦ h k hk (Nat.le_trans hkt (Nat.le_succ t)))
    funext s
    simp only [tdIterate]
    rw [ih', h (t + 1) (by omega) le_rfl]

theorem tdSourceSamplesExtend_qPolicyLiftData (M : DiscountedMDP State Action)
    (f : State → Action) (T : ℕ) (data : QSamples State Action T) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) :
    tdSourceSamplesExtend (qPolicyLiftMDP M f) T (qPolicyLiftData f data) k =
      qPolicyLiftSamples f (qSamplesExtend M T data) k := by
  funext x
  have h1 : 1 ≤ k ∧ k ≤ T := ⟨hk, hkT⟩
  have h2 : 0 < k ∧ k ≤ T := ⟨by omega, hkT⟩
  simp only [tdSourceSamplesExtend, qPolicyLiftSamples, qSamplesExtend, h1, h2,
    and_self, dite_true, qPolicyLiftData]

/-- The exact-T sampled identity on every data array. -/
theorem tdSourceSampledIterate_qPolicyLift (M : DiscountedMDP State Action)
    (f : State → Action) (η : ℕ → ℝ) (T : ℕ) (Q₀ : State → Action → ℝ)
    (data : QSamples State Action T) (x : State × Action) :
    tdSourceSampledIterate (qPolicyLiftMDP M f) qPolicyLiftPolicy η T
        (fun y ↦ Q₀ y.1 y.2) (qPolicyLiftData f data) x =
      qPolicySampledIterate M f η T Q₀ data x.1 x.2 := by
  unfold tdSourceSampledIterate qPolicySampledIterate
  rw [tdIterate_congr_samples _ _ _ _ (qPolicyLiftSamples f (qSamplesExtend M T data)) _ T
    (fun k hk hkT ↦ tdSourceSamplesExtend_qPolicyLiftData M f T data k hk hkT)]
  exact tdIterate_qPolicyLift M f η _ Q₀ T x

end StatisticalRL.QLearning
