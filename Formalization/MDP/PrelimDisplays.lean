import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.PrefixValueBridge
import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.FiniteOccupancy
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Bridges for the Chapter 2 preliminary displays

Source: arXiv:2610.41903v1, `chapters/prelim.tex:60–264` (infinite horizon) and
`:698–806` (finite horizon).

* `actionMaximum_eq_ciSup`, `qOptimality_eq_ciSup`: the Bellman optimality operator
  written with `⨆ a', Q s' a'` (the printed `max_{a'}`) is `qOptimality`.
* `trajectoryExpectedQ_eq_optimalityFixedPoint_of_optimal`: for **every** deterministic
  stationary policy whose actual trajectory Q-function dominates that of every stationary
  randomized policy, that Q-function is the optimality fixed point (mutual domination with
  the library greedy policy). This makes `Q⋆ := Q^{π⋆}` independent of the choice of `π⋆`.
* Finite horizon: `greedyDetSeq`, a deterministic Markov policy whose controlled stages
  are the library greedy stages; `finite_det_optimal_eq` shows that **every** deterministic
  Markov policy that dominates all Markov policies in `V` and `Q` at all genuine steps has
  `V_h = optimalValue` and `Q_h = optimalQ` at every step.
-/

open scoped BigOperators

namespace StatisticalRL

/-- The library maximum over a nonempty finite action set is the conditional supremum. -/
theorem actionMaximum_eq_ciSup {Action : Type*} [Fintype Action] [Nonempty Action]
    (f : Action → ℝ) : actionMaximum f = ⨆ a, f a :=
  Finset.sup'_univ_eq_ciSup f

namespace DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The Bellman optimality operator with the printed `max_{a'}` written as `⨆ a'`. -/
theorem qOptimality_eq_ciSup (M : DiscountedMDP State Action) (Q : State → Action → ℝ) :
    M.qOptimality Q = fun s a ↦
      M.reward s a + M.discount * (M.transition s a).expectation (fun s' ↦ ⨆ a', Q s' a') := by
  letI : Nonempty Action := M.action_nonempty
  funext s a
  simp only [qOptimality, actionMaximum_eq_ciSup]

/-- Every deterministic stationary policy whose actual trajectory Q-function dominates that
of every stationary randomized policy has the optimality fixed point as its Q-function. -/
theorem trajectoryExpectedQ_eq_optimalityFixedPoint_of_optimal (M : DiscountedMDP State Action)
    (f : State → Action)
    (hf : ∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
      M.trajectoryExpectedQ π s a ≤
        M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) s a) :
    M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) = M.optimalityFixedPoint := by
  funext s a
  apply le_antisymm
  · rw [← M.optimalGreedy_trajectoryQ s a]
    exact M.trajectoryQ_le_optimalGreedy _ s a
  · rw [← M.optimalGreedy_trajectoryQ s a]
    exact hf _ s a

/-- Value form: the same policies have value `max_a Q⋆(s,a)`. -/
theorem trajectoryExpectedValue_eq_of_optimal (M : DiscountedMDP State Action)
    (f g : State → Action)
    (hf : ∀ (π : StationaryPolicy State Action) (s : State),
      M.trajectoryExpectedValue π s ≤
        M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s)
    (hg : ∀ (π : StationaryPolicy State Action) (s : State),
      M.trajectoryExpectedValue π s ≤
        M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (g x)) s) :
    M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) =
      M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (g x)) := by
  funext s
  exact le_antisymm (hg _ s) (hf _ s)

end DiscountedMDP

namespace EnvironmentStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem controlled_length (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) : (controlled es π).length = es.length := by
  induction es generalizing π with
  | nil => rfl
  | cons e es ih => simp [controlled, ih]

/-- The `n`-th controlled stage is the `n`-th environment stage with decision rule `π n`. -/
theorem controlled_getElem (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (n : ℕ) (h : n < (controlled es π).length) :
    (controlled es π)[n] = (es[n]'(by simpa [controlled_length] using h)).withPolicy (π n) := by
  induction es generalizing π n with
  | nil => simp [controlled] at h
  | cons e es ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [controlled, List.getElem_cons_succ]
      exact ih (fun k ↦ π (k + 1)) n _

/-- A deterministic Markov decision sequence realizing the library greedy stages. -/
noncomputable def greedyDetSeq [Nonempty Action] :
    List (EnvironmentStage State Action) → ℕ → State → Action
  | [], _ => fun _ ↦ Classical.arbitrary Action
  | e :: es, 0 => e.greedyAction (optimalValue es)
  | _ :: es, n + 1 => greedyDetSeq es n

theorem controlled_greedyDetSeq [Nonempty Action] (es : List (EnvironmentStage State Action)) :
    controlled es (fun n s ↦ pointMass (greedyDetSeq es n s)) = greedyStages es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [controlled, greedyStages, greedyDetSeq]
    exact congrArg _ ih

/-- The deterministic greedy sequence dominates every Markov policy in `V` and `Q` at every
step (as suffix values). -/
theorem greedyDetSeq_dominates [Nonempty Action] (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (n : ℕ) (s : State) (a : Action) :
    DecisionStage.trajectoryValue ((controlled es π).drop n) s ≤
        DecisionStage.trajectoryValue
          ((controlled es (fun k x ↦ pointMass (greedyDetSeq es k x))).drop n) s ∧
    DecisionStage.trajectoryQ ((controlled es π).drop n) s a ≤
        DecisionStage.trajectoryQ
          ((controlled es (fun k x ↦ pointMass (greedyDetSeq es k x))).drop n) s a := by
  rw [controlled_greedyDetSeq]
  exact greedy_suffix_dominates es π n s a

/-- Every deterministic Markov policy that dominates all Markov policies at all genuine
steps realizes the backward-induction optimal value and action value at every step. -/
theorem finite_det_optimal_eq [Nonempty Action] (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action)
    (hf : ∀ (π : ℕ → StationaryPolicy State Action) (n : ℕ) (s : State) (a : Action),
      n < es.length →
      DecisionStage.trajectoryValue ((controlled es π).drop n) s ≤
          DecisionStage.trajectoryValue
            ((controlled es (fun k x ↦ pointMass (f k x))).drop n) s ∧
      DecisionStage.trajectoryQ ((controlled es π).drop n) s a ≤
          DecisionStage.trajectoryQ
            ((controlled es (fun k x ↦ pointMass (f k x))).drop n) s a)
    (n : ℕ) (hn : n < es.length) :
    (∀ s, DecisionStage.trajectoryValue
        ((controlled es (fun k x ↦ pointMass (f k x))).drop n) s = optimalValue (es.drop n) s) ∧
    (∀ s a, DecisionStage.trajectoryQ
        ((controlled es (fun k x ↦ pointMass (f k x))).drop n) s a = optimalQ (es.drop n) s a) := by
  have hg := hf (fun k x ↦ pointMass (greedyDetSeq es k x)) n
  rw [controlled_greedyDetSeq] at hg
  have hdom := greedy_suffix_dominates es (fun k x ↦ pointMass (f k x)) n
  refine ⟨fun s ↦ ?_, fun s a ↦ ?_⟩
  · obtain ⟨a⟩ := (inferInstance : Nonempty Action)
    have h1 := (hg s a hn).1
    have h2 := (hdom s a).1
    rw [greedy_suffix_value] at h1 h2
    exact le_antisymm h2 h1
  · have h1 := (hg s a hn).2
    rw [greedy_suffix_Q] at h1
    have h2 := (hdom s a).2
    rw [greedy_suffix_Q] at h2
    exact le_antisymm h2 h1

end EnvironmentStage
end StatisticalRL
