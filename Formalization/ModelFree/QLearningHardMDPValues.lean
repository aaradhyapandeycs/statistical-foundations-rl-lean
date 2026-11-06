import Formalization.ModelFree.QLearningHardMDPDefinitions
import Formalization.Generative.PolicyLearningPerformanceTransfer

/-!
# Optimal values of the Q-learning hard MDP (`lem:optimal-V-Q-hardMDP`)

`chapters/generative_model_model_free.tex:2797–2811`. Since rewards and transitions of
`qHardMDP` do not depend on the action, the optimal greedy policy's value is the unique
solution of a single Bellman equation, solved in closed form.
-/

open scoped BigOperators
namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP

/-- Closed-form values of `M_hard`. -/
noncomputable def qHardValue (γ : ℝ) (s : Fin 4) : ℝ :=
  if s = 0 then 0 else if s = 3 then 1 / (1 - γ) else 1 / (1 - γ * qHardP γ)

theorem qHardP_identity (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    1 / (1 - γ * qHardP γ) = 3 / (4 * (1 - γ)) := by
  have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
  have h1 : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    unfold qHardP
    field_simp
    ring
  rw [h1]
  have h2 : (1 : ℝ) - γ ≠ 0 := by intro h; linarith
  field_simp

/-- The optimal greedy policy's trajectory value is the closed form `qHardValue`. -/
theorem qHardMDP_value (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    (qHardMDP γ hγ hγ1).trajectoryExpectedValue (qHardMDP γ hγ hγ1).optimalGreedyPolicy =
      qHardValue γ := by
  let M := qHardMDP γ hγ hγ1
  have hiden : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP
    field_simp
    ring
  have hden : 0 < 1 - γ * qHardP γ := by rw [hiden]; linarith
  have hden' : 0 < 1 - γ := by linarith
  have hfix : M.valueBellman M.optimalGreedyPolicy (qHardValue γ) = qHardValue γ := by
    funext s
    change (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation (M.reward s) +
        γ * ((EnvironmentStage.pointMass (M.optimalGreedyAction s)).bind
          (M.transition s)).expectation (qHardValue γ) = qHardValue γ s
    rw [FiniteDistribution.expectation_bind, EnvironmentStage.expectation_pointMass,
      EnvironmentStage.expectation_pointMass]
    fin_cases s <;>
      simp [M, qHardMDP, qHardRow, qHardValue, FiniteDistribution.expectation, Fin.sum_univ_four]
    · field_simp
      ring
    · field_simp
      ring
    · field_simp
      ring
  have hv := (M.valueFixedPoint_characterization M.optimalGreedyPolicy (qHardValue γ)).mp hfix
  change M.trajectoryExpectedValue M.optimalGreedyPolicy = _
  rw [M.trajectoryExpectedValue_eq_valueFixedPoint]
  exact hv.symm

/-- The optimal greedy policy's trajectory Q-value at `(s, a)` is `qHardValue γ s`, for
every action `a`. -/
theorem qHardMDP_q (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (s : Fin 4) (a : Bool) :
    (qHardMDP γ hγ hγ1).trajectoryExpectedQ (qHardMDP γ hγ hγ1).optimalGreedyPolicy s a =
      qHardValue γ s := by
  let M := qHardMDP γ hγ hγ1
  have hiden : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP
    field_simp
    ring
  have hden : 0 < 1 - γ * qHardP γ := by rw [hiden]; linarith
  have hden' : 0 < 1 - γ := by linarith
  change M.trajectoryExpectedQ M.optimalGreedyPolicy s a = _
  rw [M.trajectoryQ_eq_reward_add_trajectoryValue, show M.trajectoryExpectedValue
    M.optimalGreedyPolicy = qHardValue γ from qHardMDP_value γ hγ hγ1]
  fin_cases s <;>
    simp [M, qHardMDP, qHardRow, qHardValue, FiniteDistribution.expectation, Fin.sum_univ_four]
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

/-- All values of `lem:optimal-V-Q-hardMDP`. -/
theorem qHardMDP_optimal_values (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    let M := qHardMDP γ hγ hγ1
    let Vs := M.trajectoryExpectedValue M.optimalGreedyPolicy
    let Qs := M.trajectoryExpectedQ M.optimalGreedyPolicy
    (Vs 0 = 0 ∧ ∀ a, Qs 0 a = 0) ∧
    (Vs 1 = 1 / (1 - γ * qHardP γ) ∧ (∀ a, Qs 1 a = 1 / (1 - γ * qHardP γ)) ∧
      Vs 2 = 1 / (1 - γ * qHardP γ) ∧ (∀ a, Qs 2 a = 1 / (1 - γ * qHardP γ)) ∧
      1 / (1 - γ * qHardP γ) = 3 / (4 * (1 - γ))) ∧
    (Vs 3 = 1 / (1 - γ) ∧ ∀ a, Qs 3 a = 1 / (1 - γ)) := by
  intro M Vs Qs
  have hV := qHardMDP_value γ hγ hγ1
  have hQ := qHardMDP_q γ hγ hγ1
  simp only [Vs, Qs, M, hV, hQ, qHardValue]
  refine ⟨⟨by simp, fun _ => by simp⟩, ⟨by simp, fun _ => by simp, by simp, fun _ => by simp,
    qHardP_identity γ hγ hγ1⟩, ⟨by simp, fun _ => by simp⟩⟩

end StatisticalRL.QLearning
