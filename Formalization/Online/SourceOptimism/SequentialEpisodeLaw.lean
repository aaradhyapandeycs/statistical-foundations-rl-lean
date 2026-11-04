import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Online.SourceOptimism.EpisodicStackSelector
import Formalization.MDP.FiniteTrajectory
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Sequential online law defined directly
from causal transition probabilities, independently of successor stacks. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]

theorem onlineSequentialPathHistory_length
    (choose : List (Row × Outcome) → Row) (n : ℕ)
    (history : List (Row × Outcome)) (path : OnlineOutcomePath Outcome n) :
    (onlineSequentialPathHistory choose n history path).length=history.length+n := by
  induction n generalizing history with
  | zero => simp [onlineSequentialPathHistory]
  | succ n ih =>
    rw [onlineSequentialPathHistory,ih]
    simp only [List.length_append, List.length_singleton]
    omega


end StatisticalRL.OnlineRL
