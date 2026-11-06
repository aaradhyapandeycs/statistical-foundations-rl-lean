import Formalization.Online.QLearning.Chronological
import Formalization.Online.QLearning.RateWeights

/-! actual-row visit fold. The logged target is evaluated at
its real pre-update table; this is not a source optimism or trajectory claim. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual visited records for one stage-tagged row. -/
noncomputable def qLearningRowVisits {H : ℕ} (r : OnlineMDPRow State Action H)
    (history : List (OnlineMDPRow State Action H × State)) := by
  classical
  exact history.filter (fun x => x.1 = r)

/-- Update target read from the actual table immediately before this observation. -/
noncomputable def qLearningVisitTarget {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (obs : OnlineMDPRow State Action H × State) : ℝ :=
  (E obs.1.1).reward obs.1.2.1 obs.1.2.2 +
    qLearningChronologicalValue hH E table (obs.1.1.val + 1) obs.2 +
      bonus (table.count obs.1 + 1)

/-- Retain, in order, the targets actually used at visits to r. -/
noncomputable def qLearningLoggedVisitFold {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State)) :
    QLearningChronologicalTable (State := State) (Action := Action) H × List ℝ := by
  classical
  exact history.foldl (fun acc obs =>
    (qLearningChronologicalUpdate hH E bonus acc.1 obs,
      if obs.1 = r then acc.2 ++ [qLearningVisitTarget hH E bonus acc.1 obs] else acc.2))
    (table, [])

/-- The count after arbitrary observed history is exactly its initial count
plus the number of visits to that row. -/
theorem qLearningChronologicalFold_count {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State))
    (r : OnlineMDPRow State Action H) :
    (qLearningChronologicalFold hH E bonus table history).count r =
      table.count r + (qLearningRowVisits r history).length := by
  classical
  induction history generalizing table with
  | nil => simp [qLearningChronologicalFold, qLearningRowVisits]
  | cons x xs ih =>
      have h := ih (qLearningChronologicalUpdate hH E bonus table x)
      by_cases hx : x.1 = r
      · subst r
        simpa [qLearningChronologicalFold, qLearningChronologicalUpdate,
          qLearningRowVisits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · have hr : r ≠ x.1 := Ne.symm hx
        simpa [qLearningChronologicalFold, qLearningChronologicalUpdate,
          qLearningRowVisits, hx, hr] using h

end StatisticalRL.OnlineRL
