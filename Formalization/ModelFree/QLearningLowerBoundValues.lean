import Formalization.ModelFree.QLearningLowerBoundDefinitions
import Formalization.ModelFree.QLearningHardMDPValues
import Formalization.ModelFree.QLearningIterateBounds

/-!
# Optimal values of the two-action lower-bound MDP

`lem:optimal-V-Q-hardMDP`, `chapters/generative_model_model_free.tex:2797–2811`, for `qLbMDP`:
`V⋆(0) = 0`, `V⋆(1) = V⋆(2) = 1/(1-γp) = 3/(4(1-γ))`, `V⋆(3) = 1/(1-γ)`; the source actions have
`Q⋆(s,1)` as printed and the dummy actions have `Q⋆ = 0`. Proved by exhibiting the fixed point of
the Bellman optimality operator. This is the instance used by Theorem 4.7 and Lemma 4.15; the
index entry `Lemma4_14` is stated for the copied-action encoding `qHardMDP`, which has the same
optimal values but is unsuitable for Q-learning dynamics (C31(5)).
-/

open scoped BigOperators
namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP

/-- `actionMaximum` over `Bool` is the binary maximum. -/
theorem actionMaximum_bool_max [Nonempty Bool] (f : Bool → ℝ) :
    actionMaximum f = max (f false) (f true) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun b _ ↦ by cases b <;> simp)
  · exact max_le (le_actionMaximum f false) (le_actionMaximum f true)

/-- The Q-learning value of a Bool-action array is the binary maximum. -/
theorem qLearningValue_bool {State : Type*} [Fintype State] (M : DiscountedMDP State Bool)
    (Q : State → Bool → ℝ) (s : State) :
    qLearningValue M Q s = max (Q s false) (Q s true) := by
  letI : Nonempty Bool := M.action_nonempty
  exact actionMaximum_bool_max (Q s)

/-- Candidate optimal Q-function of `qLbMDP`. -/
noncomputable def qLbQStar (γ : ℝ) (s : Fin 4) (a : Bool) : ℝ :=
  if s = 0 ∨ (s ≠ 1 ∧ a = true) then 0 else if s = 3 then 1 / (1 - γ) else 1 / (1 - γ * qHardP γ)

theorem qLb_one_sub_gamma_p (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) :
    1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
  have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
  unfold qHardP
  field_simp
  ring

theorem qLbQStar_max (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (t : Fin 4) :
    max (qLbQStar γ t false) (qLbQStar γ t true) = qHardValue γ t := by
  have h1 : 0 < 1 - γ := by linarith
  have h2 : 0 ≤ 1 / (1 - γ * qHardP γ) := by
    rw [qLb_one_sub_gamma_p γ hγ]; positivity
  have h3 : γ * qHardP γ ≤ 1 := by
    have := qLb_one_sub_gamma_p γ hγ; linarith
  have h4 : γ ≤ 1 := hγ1.le
  fin_cases t <;> simp [qLbQStar, qHardValue, h3, h4]

/-- `qLbQStar` is the Bellman optimality fixed point of `qLbMDP`. -/
theorem qLbMDP_optimalityFixedPoint (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    (qLbMDP γ hγ hγ1).optimalityFixedPoint = qLbQStar γ := by
  let M := qLbMDP γ hγ hγ1
  have hiden := qLb_one_sub_gamma_p γ hγ
  have hden : (1 : ℝ) - γ ≠ 0 := by intro h; linarith
  have hden2 : 1 - γ * qHardP γ ≠ 0 := by rw [hiden]; intro h; linarith
  symm
  apply (M.optimalityFixedPoint_characterization (qLbQStar γ)).mp
  funext s a
  letI : Nonempty Bool := M.action_nonempty
  have hmax : (fun t ↦ actionMaximum (qLbQStar γ t)) = qHardValue γ := by
    funext t
    rw [actionMaximum_bool_max]
    exact qLbQStar_max γ hγ hγ1 t
  change M.reward s a + M.discount *
    (M.transition s a).expectation (fun t ↦ actionMaximum (qLbQStar γ t)) = qLbQStar γ s a
  rw [hmax]
  fin_cases s <;> cases a <;>
    simp [M, qLbMDP, qLbRow, qHardRow, qLbQStar, qHardValue, FiniteDistribution.expectation,
      Fin.sum_univ_four]
  · field_simp
    ring_nf
  · field_simp
    ring_nf
  · field_simp
    ring_nf
  · field_simp
    ring

/-- The optimal Q-function (trajectory Q of the optimal greedy policy) of `qLbMDP`. -/
theorem qLbMDP_q (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    (qLbMDP γ hγ hγ1).trajectoryExpectedQ (qLbMDP γ hγ hγ1).optimalGreedyPolicy = qLbQStar γ := by
  funext s a
  rw [optimalGreedy_trajectoryQ, qLbMDP_optimalityFixedPoint]

/-- The optimal values of `qLbMDP` are the closed forms `qHardValue` of `lem:optimal-V-Q-hardMDP`. -/
theorem qLbMDP_value (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    (qLbMDP γ hγ hγ1).trajectoryExpectedValue (qLbMDP γ hγ hγ1).optimalGreedyPolicy =
      qHardValue γ := by
  let M := qLbMDP γ hγ hγ1
  funext s
  change M.trajectoryExpectedValue M.optimalGreedyPolicy s = _
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation
    (M.trajectoryExpectedQ M.optimalGreedyPolicy s) = _
  rw [EnvironmentStage.expectation_pointMass, optimalGreedy_trajectoryQ, optimalGreedyAction_max]
  letI : Nonempty Bool := M.action_nonempty
  rw [actionMaximum_bool_max]
  change max (M.optimalityFixedPoint s false) (M.optimalityFixedPoint s true) = _
  rw [qLbMDP_optimalityFixedPoint]
  exact qLbQStar_max γ hγ hγ1 s

/-- All values of `lem:optimal-V-Q-hardMDP` for `qLbMDP` (source actions = `false` everywhere and
`true` at state 1; dummy actions have optimal Q-value 0). -/
theorem qLbMDP_optimal_values (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    let M := qLbMDP γ hγ hγ1
    let Vs := M.trajectoryExpectedValue M.optimalGreedyPolicy
    let Qs := M.trajectoryExpectedQ M.optimalGreedyPolicy
    (Vs 0 = 0 ∧ Qs 0 false = 0) ∧
    (Vs 1 = 3 / (4 * (1 - γ)) ∧ Qs 1 false = 3 / (4 * (1 - γ)) ∧ Qs 1 true = 3 / (4 * (1 - γ)) ∧
      Vs 2 = 3 / (4 * (1 - γ)) ∧ Qs 2 false = 3 / (4 * (1 - γ))) ∧
    (Vs 3 = 1 / (1 - γ) ∧ Qs 3 false = 1 / (1 - γ)) ∧
    (Qs 0 true = 0 ∧ Qs 2 true = 0 ∧ Qs 3 true = 0) := by
  intro M Vs Qs
  have hV := qLbMDP_value γ hγ hγ1
  have hQ := qLbMDP_q γ hγ hγ1
  have hid := qHardP_identity γ hγ hγ1
  simp only [Vs, Qs, M, hV, hQ, qHardValue, qLbQStar]
  simp [hid]

end StatisticalRL.QLearning
