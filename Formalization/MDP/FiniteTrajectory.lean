import Formalization.MDP.FiniteHorizon

/-!
# Finite trajectory laws and expected episodic return

A length-indexed path records each actual action and subsequent state. Its mass
is the product of the randomized policy probabilities and transition
probabilities along that path. Cumulative reward is defined on paths before
taking the finite weighted expectation. This construction connects the source's
trajectory-return definition to finite-horizon backward evaluation.

Source: Chapter 2, Section 2.2, `eq:defn-V-pi-finite` and
`eq:Bellman-finite-pi` of arXiv:2610.41903v1.
-/

open scoped BigOperators

namespace StatisticalRL

universe u v

/-- All action/next-state paths of exactly the specified length. The current
state is supplied separately; each step stores its action and resulting state. -/
def FinitePath (State : Type u) (Action : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | n + 1 => Action × State × FinitePath State Action n

namespace FinitePath

variable {State Action : Type*}

instance instFintype [Fintype State] [Fintype Action] :
    (n : ℕ) → Fintype (FinitePath State Action n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := instFintype n
    exact inferInstanceAs (Fintype (Action × State × FinitePath State Action n))

/-- The actions actually stored in a trajectory. -/
def actions : (n : ℕ) → FinitePath State Action n → List Action
  | 0, _ => []
  | n + 1, path => path.1 :: actions n path.2.2

/-- The successive states after the supplied initial state. -/
def nextStates : (n : ℕ) → FinitePath State Action n → List State
  | 0, _ => []
  | n + 1, path => path.2.1 :: nextStates n path.2.2

@[simp]
theorem actions_length (n : ℕ) (path : FinitePath State Action n) :
    (actions n path).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [actions, List.length_cons, ih]

@[simp]
theorem nextStates_length (n : ℕ) (path : FinitePath State Action n) :
    (nextStates n path).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nextStates, List.length_cons, ih]

end FinitePath

namespace DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The joint mass of an actual action/state trajectory from the given state.
In particular, tail policies are evaluated at the sampled next state. -/
def pathWeight : (stages : List (DecisionStage State Action)) → State →
    FinitePath State Action stages.length → ℝ
  | [], _, _ => 1
  | stage :: tail, s, path =>
    (stage.policy s).prob path.1 * (stage.transition s path.1).prob path.2.1 *
      pathWeight tail path.2.1 path.2.2

/-- The actual undiscounted sum of stage rewards along a finite trajectory. -/
def pathReward : (stages : List (DecisionStage State Action)) → State →
    FinitePath State Action stages.length → ℝ
  | [], _, _ => 0
  | stage :: tail, s, path =>
    stage.reward s path.1 + pathReward tail path.2.1 path.2.2

theorem pathWeight_nonneg (stages : List (DecisionStage State Action)) (s : State)
    (path : FinitePath State Action stages.length) : 0 ≤ pathWeight stages s path := by
  induction stages generalizing s with
  | nil => exact zero_le_one
  | cons stage tail ih =>
    exact mul_nonneg
      (mul_nonneg ((stage.policy s).prob_nonneg _) ((stage.transition s path.1).prob_nonneg _))
      (ih _ _)

/-- The trajectory masses sum to one, including transitions after the final
reward. The last transition marginalizes out by its own normalization. -/
theorem sum_pathWeight (stages : List (DecisionStage State Action)) (s : State) :
    ∑ path, pathWeight stages s path = 1 := by
  induction stages generalizing s with
  | nil => simp [pathWeight, FinitePath]
  | cons stage tail ih =>
    change (∑ path : Action × State × FinitePath State Action tail.length,
      (stage.policy s).prob path.1 * (stage.transition s path.1).prob path.2.1 *
        pathWeight tail path.2.1 path.2.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ih, mul_one]
    simp only [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]

/-- A normalized finite probability law on actual trajectories of the episode. -/
def trajectoryLaw (stages : List (DecisionStage State Action)) (s : State) :
    FiniteDistribution (FinitePath State Action stages.length) where
  prob := pathWeight stages s
  prob_nonneg := pathWeight_nonneg stages s
  sum_prob := sum_pathWeight stages s

/-- Expected cumulative reward under the separately constructed trajectory law. -/
def trajectoryValue (stages : List (DecisionStage State Action)) (s : State) : ℝ :=
  (trajectoryLaw stages s).expectation (pathReward stages s)

/-- Finite-sum conditioning on the first actual action and next state. This
holds for any payoff on whole paths, before specializing to cumulative reward. -/
theorem trajectoryExpectation_cons (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State)
    (f : FinitePath State Action (stage :: tail).length → ℝ) :
    (trajectoryLaw (stage :: tail) s).expectation f =
      (stage.policy s).expectation (fun a ↦
        (stage.transition s a).expectation (fun t ↦
          (trajectoryLaw tail t).expectation (fun path ↦ f (a, t, path)))) := by
  change (∑ path : Action × State × FinitePath State Action tail.length,
      ((stage.policy s).prob path.1 * (stage.transition s path.1).prob path.2.1 *
        pathWeight tail path.2.1 path.2.2) * f path) = _
  simp only [FiniteDistribution.expectation, trajectoryLaw,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

@[simp]
theorem trajectoryValue_nil (s : State) :
    trajectoryValue ([] : List (DecisionStage State Action)) s = 0 := by
  exact (trajectoryLaw [] s).expectation_const 0

/-- The trajectory expectation satisfies the first-step Bellman decomposition.
Normalization, rather than an assumed Bellman law, removes future constant rewards. -/
theorem trajectoryValue_cons (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) :
    trajectoryValue (stage :: tail) s = stage.valueBackup (trajectoryValue tail) s := by
  unfold trajectoryValue
  rw [trajectoryExpectation_cons]
  change (stage.policy s).expectation (fun a ↦
      (stage.transition s a).expectation (fun t ↦
        (trajectoryLaw tail t).expectation (fun path ↦
          stage.reward s a + pathReward tail t path))) = _
  simp_rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
  exact ((stage.policy s).expectation_add _ _).symm

/-- The source's expected cumulative trajectory reward equals backward policy
evaluation for arbitrary time-varying transition kernels, rewards and policies. -/
theorem trajectoryValue_eq_backwardValue (stages : List (DecisionStage State Action))
    (s : State) : trajectoryValue stages s = backwardValue stages s := by
  induction stages generalizing s with
  | nil => exact trajectoryValue_nil s
  | cons stage tail ih =>
    have htail : trajectoryValue tail = backwardValue tail := funext ih
    rw [trajectoryValue_cons, backwardValue_cons, htail]

end DecisionStage

end StatisticalRL
