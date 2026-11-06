import Formalization.Online.QLearning.ActualOptimismConfidence

/-! Actual Q-learning policy is the fixed greedy selector of its table. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem qLearningChronologicalPolicy_max {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (h : Fin H) (s : State) :
    table.q (h,(s,qLearningChronologicalPolicy E table h s)) =
      letI : Nonempty Action := (E h).action_nonempty
      actionMaximum (fun a => table.q (h,(s,a))) := by
  letI : Nonempty Action := (E h).action_nonempty
  exact Classical.choose_spec (EnvironmentStage.exists_maximizer (fun a => table.q (h,(s,a))))

theorem qLearningChronologicalValue_le_greedyQ {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (h : Fin H) (s : State) :
    qLearningChronologicalValue hH E table h.val s ≤
      table.q (h,(s,qLearningChronologicalPolicy E table h s)) := by
  letI : Nonempty Action := (E h).action_nonempty
  rw [qLearningChronologicalPolicy_max]
  unfold qLearningChronologicalValue
  simp only [dif_pos h.isLt]
  exact min_le_right _ _
end StatisticalRL.OnlineRL
