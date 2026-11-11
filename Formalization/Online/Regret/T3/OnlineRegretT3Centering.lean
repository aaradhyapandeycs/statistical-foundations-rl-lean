import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.SourceOptimism.SequentialHistoryDensity

/-!
# Actual sequential kernel centering for the UCBVI T₃ increment

component auxiliary module. This proves a one-step centering identity under
the recursive direct sequential law at an arbitrary revealed history. It does
not yet identify that identity with a conditional expectation under the full
reset-vector/history filtration, and it proves no Freedman tail or regret
bound. It uses the corrected zero-count-safe capped planner from the existing
regret telescope.
-/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The source continuation `V_{h+1}^k` selected from completed episodes only.
The observed history may include the current episode prefix, but planning uses
only its first `k*H` records, matching the causal planner. -/
noncomputable def onlineT3CompletedPrefixTail {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) (h : Fin H)
    (L c₁ c₂ : ℝ) : State → ℝ :=
  onlineCappedBackwardValue (H : ℝ) L c₁ c₂
    ((List.ofFn (fun j : Fin H =>
      onlineHistoryPlanningStage E (history.take (k * H)) j)).drop (h.val + 1))

/-- For any starting transcript, the first successor under the actual
recursive sequential outcome law has exactly the selected row's distribution.
The suffix may be arbitrarily long; its normalization is summed out. -/
theorem onlineSequentialOutcomeLaw_firstSuccessor_expectation
    {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row)
    (n : ℕ) (history : List (Row × Outcome)) (f : Outcome → ℝ) :
    (onlineSequentialOutcomeLaw d choose (n + 1) history).expectation
        (fun path => f path.2.1) = (d (choose history)).expectation f := by
  classical
  simp only [FiniteDistribution.expectation]
  change
      (∑ path : PUnit × Outcome × OnlineOutcomePath Outcome n,
        ((d (choose history)).prob path.2.1 *
          (onlineSequentialOutcomeLaw d choose n
            (history ++ [(choose history, path.2.1)])).prob path.2.2) *
          f path.2.1) =
        ∑ x : Outcome, (d (choose history)).prob x * f x
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ tail : OnlineOutcomePath Outcome n,
        ((d (choose history)).prob x *
          (onlineSequentialOutcomeLaw d choose n
            (history ++ [(choose history, x)])).prob tail) * f x) =
        ((d (choose history)).prob x * f x) *
          ∑ tail : OnlineOutcomePath Outcome n,
            (onlineSequentialOutcomeLaw d choose n
              (history ++ [(choose history, x)])).prob tail := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail htail
      ring
    _ = (d (choose history)).prob x * f x := by
      rw [(onlineSequentialOutcomeLaw d choose n
        (history ++ [(choose history, x)] )).sum_prob]
      ring

end StatisticalRL.OnlineRL
