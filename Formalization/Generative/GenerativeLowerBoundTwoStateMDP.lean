import Formalization.Generative.GenerativeLowerBoundParameters
import Formalization.Generative.PolicyLearningPerformanceTransfer

/-! Actual source two-state, one-action lower-bound MDP. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.DiscountedMDP

/-- The source transition: true is the rewarding state, false is absorbing. -/
noncomputable def hardRow (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : Bool) : FiniteDistribution Bool where
  prob t := if t then (if s then p else 0) else (if s then 1 - p else 1)
  prob_nonneg := by intro t; cases s <;> cases t <;> simp_all
  sum_prob := by cases s <;> simp

/-- Two-state source model with known deterministic rewards and one action. -/
noncomputable def hardMDP (γ p : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : DiscountedMDP Bool Unit where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition s _ := hardRow p hp hp1 s
  reward s _ := if s then 1 else 0
  reward_nonneg := by intro s a; cases s <;> simp
  reward_le_one := by intro s a; cases s <;> simp
  discount := γ
  discount_nonneg := hγ
  discount_lt_one := hγ1

/-- The sole deterministic policy. -/
noncomputable def onlyPolicy : StationaryPolicy Bool Unit :=
  fun _ ↦ EnvironmentStage.pointMass ()

/-- The model's optimal greedy policy is its unique policy. -/
theorem hardMDP_optimalGreedy_eq_only (γ p : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (hardMDP γ p hγ hγ1 hp hp1).optimalGreedyPolicy = onlyPolicy := by
  funext s
  simp [DiscountedMDP.optimalGreedyPolicy, onlyPolicy, Subsingleton.elim
    ((hardMDP γ p hγ hγ1 hp hp1).optimalGreedyAction s) ()]

/-- A closed form satisfies the actual model's policy Bellman equation. -/
theorem hardMDP_trajectory_value (γ p : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (hardMDP γ p hγ hγ1 hp hp1).trajectoryExpectedValue onlyPolicy =
      fun s ↦ if s then 1 / (1 - γ * p) else 0 := by
  let M := hardMDP γ p hγ hγ1 hp hp1
  let V : Bool → ℝ := fun s ↦ if s then 1 / (1 - γ * p) else 0
  have hden : 0 < 1 - γ * p := by
    have := mul_le_mul_of_nonneg_left hp1 hγ
    nlinarith
  have hfix : M.valueBellman onlyPolicy V = V := by
    funext s
    change (EnvironmentStage.pointMass ()).expectation (M.reward s) + γ *
      ((EnvironmentStage.pointMass ()).bind (M.transition s)).expectation V = V s
    rw [FiniteDistribution.expectation_bind, EnvironmentStage.expectation_pointMass,
      EnvironmentStage.expectation_pointMass]
    cases s <;> simp [M, hardMDP, FiniteDistribution.expectation, hardRow, V]
    field_simp
    ring
  have hv := (M.valueFixedPoint_characterization onlyPolicy V).mp hfix
  rw [M.trajectoryExpectedValue_eq_valueFixedPoint]
  exact hv.symm

/-- Actual trajectory-optimal Q at the rewarding state is the source
closed form; this is a derived fact about the constructed MDP. -/
theorem hardMDP_optimalQ_true (γ p : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let M := hardMDP γ p hγ hγ1 hp hp1
    M.trajectoryExpectedQ M.optimalGreedyPolicy true () = 1 / (1 - γ * p) := by
  let M := hardMDP γ p hγ hγ1 hp hp1
  have hden : 0 < 1 - γ * p := by
    have := mul_le_mul_of_nonneg_left hp1 hγ
    nlinarith
  change M.trajectoryExpectedQ M.optimalGreedyPolicy true () = _
  rw [show M.optimalGreedyPolicy = onlyPolicy from hardMDP_optimalGreedy_eq_only γ p hγ hγ1 hp hp1,
    M.trajectoryQ_eq_reward_add_trajectoryValue,
    show M.trajectoryExpectedValue onlyPolicy = (fun s ↦ if s then 1 / (1 - γ * p) else 0) from
      hardMDP_trajectory_value γ p hγ hγ1 hp hp1]
  simp [M, hardMDP, FiniteDistribution.expectation, hardRow]
  field_simp
  ring

/-- The two source hard instances, with the hypotheses discharging all
probability and discount obligations. -/
noncomputable def sourceHardMDP (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (i : Bool) :
    DiscountedMDP Bool Unit := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  let p := if i then baseProbability γ + probabilityIncrement γ ε else baseProbability γ
  have hp : 0 ≤ p := by dsimp [p]; split <;> linarith [ha.1, ha.2.1]
  have hp1 : p ≤ 1 := by dsimp [p]; split <;> linarith [ha.2.1, ha.2.2.1]
  exact hardMDP γ p (by linarith) hγ1 hp hp1

/-- The two actual trajectory-optimal forced-action Q values in the source
construction are separated strictly by more than 2ε. -/
theorem sourceHardMDP_optimalQ_separation (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    let M₀ := sourceHardMDP γ ε hγ hγ1 hε hεmax false
    let M₁ := sourceHardMDP γ ε hγ hγ1 hε hεmax true
    2 * ε < M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy true () -
      M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy true () := by
  dsimp only [sourceHardMDP]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hardMDP_optimalQ_true, hardMDP_optimalQ_true]
  exact source_parameters_scalar_separation γ ε hγ hγ1 hε hεmax

end StatisticalRL.GenerativeLowerBound
