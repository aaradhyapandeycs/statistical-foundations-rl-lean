import Formalization.Online.QLearning.OptimalSuffixRange

/-! Terminal continuation has zero noise; in particular the H=1 endpoint. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem qLearningTrueOptimalNext_last_zero {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (r : OnlineMDPRow State Action H)
    (hr : r.1.val+1 = H) : qLearningTrueOptimalNext E r = fun _ => 0 := by
  funext s
  unfold qLearningTrueOptimalNext
  rw [hr]
  have hd : (List.ofFn E).drop H = [] := by
    apply List.drop_eq_nil_of_le
    simp
  simp [hd, EnvironmentStage.optimalValue]

theorem qLearningTerminal_centeredSample_zero {H n : ℕ}
    (E : Fin H → EnvironmentStage State Action) (r : OnlineMDPRow State Action H)
    (hr : r.1.val+1 = H) (i : Fin n) (ω : Fin n → State) :
    (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) n i ω = 0 := by
  rw [qLearningTrueOptimalNext_last_zero E r hr]
  simp [FiniteDistribution.centeredSample, FiniteDistribution.expectation_const]
end StatisticalRL.OnlineRL
