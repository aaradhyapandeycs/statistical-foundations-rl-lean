import Formalization.MDP.DecisionStageDefinitions
import Formalization.MDP.Basic

/-!
# Backward policy evaluation over a finite episode

This file implements the finite-horizon Bellman recursions from Chapter 2,
Section 2.2 of arXiv:2610.41903v1. A list stores the actual remaining stages,
so its empty suffix is the terminal stage and introduces no off-domain defaults.
The stages may have different transition kernels, reward functions, and policies.
The identification with the paper's independently defined trajectory expectation
remains a separate obligation; these are proved backward-evaluation facts.
-/

namespace StatisticalRL

namespace DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem valueBackup_nonneg (stage : DecisionStage State Action) {V : State → ℝ}
    (h : ∀ s, 0 ≤ V s) (s : State) : 0 ≤ stage.valueBackup V s := by
  apply (stage.policy s).expectation_nonneg
  intro a
  exact add_nonneg (stage.reward_nonneg s a) ((stage.transition s a).expectation_nonneg h)

theorem valueBackup_le (stage : DecisionStage State Action) {V : State → ℝ} {c : ℝ}
    (h : ∀ s, V s ≤ c) (s : State) : stage.valueBackup V s ≤ 1 + c := by
  apply (stage.policy s).expectation_le_const
  intro a
  exact add_le_add (stage.reward_le_one s a) ((stage.transition s a).expectation_le_const h)

/-- Pointwise nonexpansiveness of the undiscounted policy-evaluation backup. -/
theorem abs_valueBackup_sub_le (stage : DecisionStage State Action)
    {V₁ V₂ : State → ℝ} {ε : ℝ} (h : ∀ s, |V₁ s - V₂ s| ≤ ε) (s : State) :
    |stage.valueBackup V₁ s - stage.valueBackup V₂ s| ≤ ε := by
  apply (stage.policy s).abs_expectation_sub_le
  intro a
  simpa only [qBackup, add_sub_add_left_eq_sub] using
    (stage.transition s a).abs_expectation_sub_le h

/-- Backward evaluation of a finite sequence of controlled MDP stages. -/
def backwardValue : List (DecisionStage State Action) → State → ℝ
  | [] => fun _ ↦ 0
  | stage :: tail => stage.valueBackup (backwardValue tail)

@[simp]
theorem backwardValue_nil (s : State) :
    backwardValue ([] : List (DecisionStage State Action)) s = 0 := rfl

@[simp]
theorem backwardValue_cons (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) :
    backwardValue (stage :: tail) s = stage.valueBackup (backwardValue tail) s := rfl

theorem backwardValue_nonneg (stages : List (DecisionStage State Action)) (s : State) :
    0 ≤ backwardValue stages s := by
  induction stages generalizing s with
  | nil => exact le_refl 0
  | cons stage tail ih =>
    exact stage.valueBackup_nonneg (fun t ↦ ih t) s

/-- The return computed by backward evaluation lies below the number of remaining stages. -/
theorem backwardValue_le_length (stages : List (DecisionStage State Action)) (s : State) :
    backwardValue stages s ≤ (stages.length : ℝ) := by
  induction stages generalizing s with
  | nil => simp [backwardValue]
  | cons stage tail ih =>
    calc
      backwardValue (stage :: tail) s ≤ 1 + (tail.length : ℝ) :=
        stage.valueBackup_le (fun t ↦ ih t) s
      _ = ((stage :: tail).length : ℝ) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

end DecisionStage

end StatisticalRL
