import Formalization.ModelFree.QLearningRobustBallCompact

/-! compact-ball optimizers are attained extrema of
  the robust expectation image used by the Bellman operators. -/
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The supremum in the robust Bellman operator is the expectation of an
actual feasible distribution, rather than merely a least upper bound. -/
theorem qRobustExpectations_sup_attained (p : FiniteDistribution State)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (v : State → ℝ) :
    ∃ z ∈ qRobustExpectations p ρ v,
      ∀ w ∈ qRobustExpectations p ρ v, w ≤ z := by
  obtain ⟨q, hq, hmax⟩ := (qChiBall_extrema_attained p ρ hρ v).1
  refine ⟨q.expectation v, ?_, ?_⟩
  · exact ⟨q, hq, rfl⟩
  · intro w hw
    rcases hw with ⟨d, hd, rfl⟩
    exact hmax d hd

/-- The infimum in the robust Bellman operator is the expectation of an
actual feasible distribution. -/
theorem qRobustExpectations_inf_attained (p : FiniteDistribution State)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (v : State → ℝ) :
    ∃ z ∈ qRobustExpectations p ρ v,
      ∀ w ∈ qRobustExpectations p ρ v, z ≤ w := by
  obtain ⟨q, hq, hmin⟩ := (qChiBall_extrema_attained p ρ hρ v).2
  refine ⟨q.expectation v, ?_, ?_⟩
  · exact ⟨q, hq, rfl⟩
  · intro w hw
    rcases hw with ⟨d, hd, rfl⟩
    exact hmin d hd

end StatisticalRL.QLearning
