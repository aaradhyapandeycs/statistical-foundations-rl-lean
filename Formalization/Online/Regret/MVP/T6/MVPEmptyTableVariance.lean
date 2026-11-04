import Formalization.Online.SourceOptimism.CappedBackwardRecursion
import Formalization.Probability.Variance

/-! Uncompiled K=1 ingredient: if the retained observations are empty,
every tail value is constant, including the terminal zero tail. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvp_emptyStages_value_constant
    (cap L c₁ c₂ : ℝ) (stages : List (OnlineObservedPlanningStage State Action))
    (hzero : ∀ stage ∈ stages, ∀ s a, (stage.observations s a).length = 0) :
    ∃ c : ℝ, ∀ s, onlineCappedBackwardValue cap L c₁ c₂ stages s = c := by
  cases stages with
  | nil => exact ⟨0, fun _ => rfl⟩
  | cons stage tail =>
    refine ⟨cap, ?_⟩
    intro s
    letI : Nonempty Action := stage.environment.action_nonempty
    obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer
      (onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s)
    change actionMaximum _ = cap
    rw [← ha]
    exact onlineCappedStageQ_zero_count cap L c₁ c₂ stage _ s a
      (hzero stage (by simp) s a)

theorem mvp_emptyStages_tail_variance_zero
    (cap L c₁ c₂ : ℝ) (stages : List (OnlineObservedPlanningStage State Action))
    (hzero : ∀ stage ∈ stages, ∀ s a, (stage.observations s a).length = 0)
    (n : ℕ) (p : FiniteDistribution State) :
    p.variance (onlineCappedBackwardValueAt cap L c₁ c₂ stages n) = 0 := by
  have hz : ∀ stage ∈ stages.drop n, ∀ s a, (stage.observations s a).length = 0 := by
    intro stage hs
    exact hzero stage (List.mem_of_mem_drop hs)
  obtain ⟨c,hc⟩ := mvp_emptyStages_value_constant cap L c₁ c₂ (stages.drop n) hz
  have heq : onlineCappedBackwardValueAt cap L c₁ c₂ stages n = fun _ => c := by
    funext s
    exact hc s
  rw [heq, FiniteDistribution.variance_const]
end StatisticalRL.OnlineRL
