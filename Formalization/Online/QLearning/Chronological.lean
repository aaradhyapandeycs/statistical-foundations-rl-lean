import Formalization.Online.QLearning.ChronologicalDefinitions

/-! Q-learning table fold and stage-locality candidate.
A later bridge must identify the list with the actual sequential episode law. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Updates at stages strictly before g leave every g-or-later row unchanged. -/
theorem qLearningChronologicalFold_later {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State)) (g : ℕ)
    (histages : ∀ x ∈ history, x.1.1.val < g)
    (r : OnlineMDPRow State Action H) (hr : g ≤ r.1.val) :
    (qLearningChronologicalFold hH E bonus table history).q r = table.q r ∧
    (qLearningChronologicalFold hH E bonus table history).count r = table.count r := by
  classical
  induction history generalizing table with
  | nil => simp [qLearningChronologicalFold]
  | cons x xs ih =>
      have hx : x.1.1.val < g := histages x (by simp)
      have hxs : ∀ y ∈ xs, y.1.1.val < g := by
        intro y hy
        exact histages y (by simp [hy])
      have hne : r ≠ x.1 := by
        intro he
        have hh : r.1.val = x.1.1.val := congrArg (fun z => z.1.val) he
        omega
      have hfold := ih (qLearningChronologicalUpdate hH E bonus table x) hxs
      simpa [qLearningChronologicalFold, qLearningChronologicalUpdate, hne] using hfold

/-- In particular, the next-stage value is the pre-episode value; the
terminal case is zero by the same definition. -/
theorem qLearningChronologicalFold_later_value {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State)) (g : ℕ)
    (histages : ∀ x ∈ history, x.1.1.val < g) (s : State) :
    qLearningChronologicalValue hH E (qLearningChronologicalFold hH E bonus table history) g s =
      qLearningChronologicalValue hH E table g s := by
  classical
  unfold qLearningChronologicalValue
  split
  next hg =>
    letI : Nonempty Action := (E ⟨g,hg⟩).action_nonempty
    congr 1
    apply congrArg actionMaximum
    funext a
    exact (qLearningChronologicalFold_later hH E bonus table history g histages
      (⟨g,hg⟩,(s,a)) (by simp)).1
  next => rfl

end StatisticalRL.OnlineRL
