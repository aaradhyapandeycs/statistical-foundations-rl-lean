import Formalization.Online.QLearning.ActualErrorBounds

/-! Pointwise Bellman max/cap transfer for the actual chronological table. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- If each true action value is below its table value at a stage, the capped
actual table value is also optimistic at that stage. -/
theorem qLearning_value_ge_optimal_of_q {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (h : Fin H) (s : State)
    (hQ : ∀ a, qLearningTrueOptimalQ E (h,(s,a)) ≤ table.q (h,(s,a))) :
    EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      qLearningChronologicalValue hH E table h.val s := by
  classical
  letI : Nonempty Action := (E h).action_nonempty
  have hlen : ((List.ofFn E).drop h.val).length ≤ H := by simp
  have htruth := (onlineTrueOptimalValue_range_length ((List.ofFn E).drop h.val) s).2
  have hcap : EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤ (H:ℝ) := by
    have hh : (((List.ofFn E).drop h.val).length:ℝ) ≤ H := by exact_mod_cast hlen
    exact htruth.trans hh
  have hnext : EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s =
      actionMaximum (fun a => qLearningTrueOptimalQ E (h,(s,a))) := by
    have hj : h.val < (List.ofFn E).length := by simpa using h.isLt
    rw [List.drop_eq_getElem_cons hj]
    simp [EnvironmentStage.optimalValue,EnvironmentStage.qBackup,qLearningTrueOptimalQ,
      qLearningTrueOptimalNext,List.getElem_ofFn]
    rfl
  obtain ⟨a,ha⟩ := EnvironmentStage.exists_maximizer (fun a => qLearningTrueOptimalQ E (h,(s,a)))
  have hmax : EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      actionMaximum (fun a => table.q (h,(s,a))) := by
    rw [hnext,← ha]
    exact (hQ a).trans (le_actionMaximum (fun b : Action => table.q (h,(s,b))) a)
  unfold qLearningChronologicalValue
  simp only [dif_pos h.isLt]
  exact le_min hcap hmax
end StatisticalRL.OnlineRL
