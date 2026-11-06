import Formalization.Online.QLearning.LoggedIndex

/-! algebra for turning real chronological updates into
ordered episode blocks. The final source-index list equality remains open. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- Starting with a log priorLog prepends that priorLog to precisely the targets
collected by the same real table fold. -/
theorem qLearningLogFrom_prefix {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (priorLog : List ℝ) (history : List (OnlineMDPRow State Action H × State)) :
    (qLearningLogFrom hH E bonus r (table,priorLog) history).2 =
      priorLog ++ (qLearningLoggedVisitFold hH E bonus r table history).2 := by
  classical
  induction history generalizing table priorLog with
  | nil => simp [qLearningLogFrom, qLearningLoggedVisitFold]
  | cons x xs ih =>
      change (qLearningLogFrom hH E bonus r
        (qLearningChronologicalUpdate hH E bonus table x,
          if x.1 = r then priorLog ++ [qLearningVisitTarget hH E bonus table x] else priorLog) xs).2 =
        priorLog ++ (qLearningLogFrom hH E bonus r
          (qLearningChronologicalUpdate hH E bonus table x,
            if x.1 = r then [qLearningVisitTarget hH E bonus table x] else []) xs).2
      rw [ih, ih]
      by_cases hx : x.1 = r <;> simp [hx, List.append_assoc]

/-- Concatenating observations appends their target log, evaluated from the
actual table produced by the first segment. -/
theorem qLearningLoggedVisitFold_append {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (r : OnlineMDPRow State Action H)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (first second : List (OnlineMDPRow State Action H × State)) :
    (qLearningLoggedVisitFold hH E bonus r table (first ++ second)).2 =
      (qLearningLoggedVisitFold hH E bonus r table first).2 ++
      (qLearningLoggedVisitFold hH E bonus r
        (qLearningChronologicalFold hH E bonus table first) second).2 := by
  classical
  rw [qLearningLogged_eq_from]
  simp only [qLearningLogFrom, List.foldl_append]
  change (qLearningLogFrom hH E bonus r
    (qLearningLoggedVisitFold hH E bonus r table first) second).2 = _
  rw [qLearningLogFrom_prefix]
  rw [qLearningLogged_eq_from, qLearningLogFrom_q]

end StatisticalRL.OnlineRL
