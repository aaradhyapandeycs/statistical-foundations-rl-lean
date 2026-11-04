import Formalization.Online.Regret.PolicyVariance.FiniteTrajectoryVarianceBudget

/-! Source finite-policy expected cumulative transition variance ≤ horizon²,
under the actual controlled trajectory law. This does not yet transport the
fixed policy into an adaptive episode conditional law. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem finiteTrajectory_pathReward_range
    (stages : List (DecisionStage State Action)) (s : State)
    (path : FinitePath State Action stages.length) :
    0 ≤ DecisionStage.pathReward stages s path ∧
      DecisionStage.pathReward stages s path ≤ stages.length := by
  induction stages generalizing s with
  | nil => simp [DecisionStage.pathReward]
  | cons stage tail ih =>
      rcases path with ⟨a, t, rest⟩
      have hh := ih t rest
      simp only [DecisionStage.pathReward, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor
      · exact add_nonneg (stage.reward_nonneg s a) hh.1
      · linarith [stage.reward_le_one s a, hh.2]

/-- For any fixed controlled finite episode, the actual trajectory expectation
of the sum of successor-value transition variances is bounded by H². The
statement even permits randomized within-episode policies; the source fixed
deterministic policy is a specialization. -/
theorem finiteTrajectory_expected_variance_le_horizon_sq
    (stages : List (DecisionStage State Action)) (s : State) :
    (DecisionStage.trajectoryLaw stages s).expectation (finiteTrajectoryVarianceSum stages s) ≤
      (stages.length : ℝ)^2 := by
  apply (finiteTrajectory_expected_variance_le_return_variance stages s).trans
  apply ((DecisionStage.trajectoryLaw stages s).variance_le_expectation_sq _).trans
  apply (DecisionStage.trajectoryLaw stages s).expectation_le_const
  intro path
  have hh := finiteTrajectory_pathReward_range stages s path
  have hN : (0 : ℝ) ≤ stages.length := Nat.cast_nonneg _
  nlinarith [sq_nonneg ((stages.length : ℝ) - DecisionStage.pathReward stages s path)]
end StatisticalRL.OnlineRL
