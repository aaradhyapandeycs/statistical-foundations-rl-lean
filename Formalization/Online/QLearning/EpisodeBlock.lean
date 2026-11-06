import Formalization.Online.QLearning.TargetLogAppend

/-! deterministic block algebra. The actual sequential
stage decomposition must subsequently discharge the block hypotheses. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- A history with no visit to r contributes no target to r's actual log. -/
theorem qLearningLoggedVisitFold_noVisits {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State))
    (hnot : ∀ x ∈ history, x.1 ≠ r) :
    (qLearningLoggedVisitFold hH E bonus r table history).2 = [] := by
  classical
  induction history generalizing table with
  | nil => rfl
  | cons x xs ih =>
      have hx : x.1 ≠ r := hnot x (by simp)
      have hxs : ∀ y ∈ xs, y.1 ≠ r := by
        intro y hy
        exact hnot y (by simp [hy])
      simp only [qLearningLoggedVisitFold, List.foldl_cons, hx, if_false]
      change (qLearningLogFrom hH E bonus r
        (qLearningChronologicalUpdate hH E bonus table x, []) xs).2 = []
      simpa [qLearningLogged_eq_from] using ih
        (qLearningChronologicalUpdate hH E bonus table x) hxs

/-- A single stage-block with at most the designated matching record adds its
actual pre-update target, with no change of continuation convention. -/
theorem qLearningLoggedVisitFold_singleMatch {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (before after : List (OnlineMDPRow State Action H × State))
    (obs : OnlineMDPRow State Action H × State)
    (hb : ∀ x ∈ before, x.1 ≠ r) (ha : ∀ x ∈ after, x.1 ≠ r) :
    (qLearningLoggedVisitFold hH E bonus r table (before ++ [obs] ++ after)).2 =
      if obs.1 = r then [qLearningVisitTarget hH E bonus
        (qLearningChronologicalFold hH E bonus table before) obs] else [] := by
  classical
  rw [List.append_assoc, qLearningLoggedVisitFold_append]
  rw [qLearningLoggedVisitFold_noVisits hH E bonus r table before hb]
  simp only [List.nil_append]
  rw [show [obs] ++ after = [obs] ++ after by rfl, qLearningLoggedVisitFold_append]
  rw [qLearningLoggedVisitFold_noVisits hH E bonus r _ after ha]
  simp [qLearningLoggedVisitFold, qLearningChronologicalFold,
    qLearningVisitTarget, List.foldl_cons, List.foldl_nil]

end StatisticalRL.OnlineRL
