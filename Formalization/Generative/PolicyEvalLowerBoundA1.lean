import Formalization.Generative.PolicyLearningFixedPolicyProjection
import Formalization.Generative.GenerativeLowerBoundTheorem37Fin
import Formalization.MDP.ForcedPrefixBridge

/-!
# Policy-evaluation minimax lower bound with a single action

Source: `theorem:azar`, `source/upstream/tex/chapters/generative_model_model_based.tex:1443–1464`,
specialized to `A = 1` as used by the comparisons at
`generative_model_model_based.tex:1468–1474` (policy evaluation against Theorem 3.1) and
`generative_model_model_free.tex:248–249` (TD learning against Theorem 3.7 with `A = 1`).

With one action there is a unique stationary policy `π₀`, `Q⋆(s, 0) = V^{π₀}(s)`, and the
learning sample array restricted along `π₀` has exactly the policy-evaluation sampling law
(`samplingLaw_projectPolicySamples`). Any deterministic value estimator built from
policy-evaluation samples therefore induces a Q-estimator on learning samples, and the
corrected Theorem 3.7 part (ii) (`theorem37_corrected_fin_carriers`, which needs only
`S ≥ 2`, implied here by `S = SA ≥ 16`) transfers to it.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.GenerativeLowerBound

open StatisticalRL.DiscountedMDP

local instance policyEvalA1FinMeasurable (S : ℕ) : MeasurableSpace (Fin S) := ⊤

/-- The unique stationary policy with a single action. -/
noncomputable abbrev singleActionPolicy (S : ℕ) : StationaryPolicy (Fin S) (Fin 1) :=
  fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1)

theorem singleAction_optimalGreedyPolicy_eq {S : ℕ} (M : DiscountedMDP (Fin S) (Fin 1)) :
    M.optimalGreedyPolicy = singleActionPolicy S := by
  funext s
  change EnvironmentStage.pointMass (M.optimalGreedyAction s) = _
  rw [Subsingleton.elim (M.optimalGreedyAction s) 0]

theorem singleAction_trajectoryExpectedQ_eq {S : ℕ} (M : DiscountedMDP (Fin S) (Fin 1))
    (s : Fin S) (a : Fin 1) :
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a =
      M.trajectoryExpectedValue (singleActionPolicy S) s := by
  rw [singleAction_optimalGreedyPolicy_eq, M.trajectoryExpectedValue_eq_policyAverageQ,
    EnvironmentStage.expectation_pointMass, Subsingleton.elim a 0]

theorem norm_singleAction_lift {S : ℕ} (h : Fin S → ℝ) :
    ‖((fun s _ ↦ h s : Fin S → Fin 1 → ℝ))‖ = ‖h‖ := by
  set g : Fin S → Fin 1 → ℝ := fun s _ ↦ h s with hg
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun s ↦ ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun _ ↦ ?_
    exact norm_le_pi_norm h s
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun s ↦ ?_
    have h1 : ‖g s 0‖ ≤ ‖g s‖ := norm_le_pi_norm (g s) 0
    have h2 : ‖g s‖ ≤ ‖g‖ := norm_le_pi_norm g s
    exact h1.trans h2

/-- Policy-evaluation lower bound at `A = 1` (Theorem 3.7(ii) with a single action):
every deterministic value estimator that sees the known reward table, the known discount and
`N` policy-transition samples per state has probability at least `1/4` of sup-norm error
exceeding `ε` on some `γ`-discounted MDP with `S` states, whenever `S ≥ 16`,
`γ ∈ [2/3, 1)`, `0 < ε < 1/(32(1−γ))` and `N ≤ (1/32768) log S / ((1−γ)³ε²)`. -/
theorem policyEvaluation_lowerBound_singleAction :
    ∀ (S N : ℕ) (γ ε : ℝ),
      16 ≤ S → (2 : ℝ) / 3 ≤ γ → γ < 1 → 0 < ε → ε < 1 / (32 * (1 - γ)) →
      (N : ℝ) ≤ (1 / 32768) * Real.log (S : ℝ) / ((1 - γ) ^ 3 * ε ^ 2) →
      ∀ VHat : (Fin S → Fin 1 → ℝ) → ℝ →
          StatisticalRL.ModelBasedPolicyEvaluation.Samples (Fin S) N → Fin S → ℝ,
        ∃ M : DiscountedMDP (Fin S) (Fin 1), M.discount = γ ∧
          (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M
              (fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1)) N).real
            {data | ε < ‖VHat M.reward M.discount data -
              M.trajectoryExpectedValue (fun _ ↦ EnvironmentStage.pointMass (0 : Fin 1))‖} := by
  intro S N γ ε hS hγ hγ1 hε hεmax hN VHat
  have hN' : (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * ((1 : ℕ) : ℝ)) /
      ((1 - γ) ^ 3 * ε ^ 2) := by
    simpa using hN
  let f : Fin S → Fin 1 := fun _ ↦ 0
  let QHat : (Fin S → Fin 1 → ℝ) → ℝ →
      StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin 1) N → Fin S → Fin 1 → ℝ :=
    fun r g data s _ ↦ VHat r g (ModelBasedPolicyLearning.projectPolicySamples N f data) s
  obtain ⟨M, hMγ, hrisk⟩ :=
    (theorem37_corrected_fin_carriers S 1 N γ ε (by omega) (by omega) hγ hγ1 hε hεmax hN').2
      QHat
  refine ⟨M, hMγ, ?_⟩
  let target : Set (StatisticalRL.ModelBasedPolicyEvaluation.Samples (Fin S) N) :=
    {data | ε < ‖VHat M.reward M.discount data -
      M.trajectoryExpectedValue (singleActionPolicy S)‖}
  have hmeas : MeasurableSet target := (Set.to_countable _).measurableSet
  change (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M
    (fun t ↦ EnvironmentStage.pointMass (f t)) N).real target
  rw [← ModelBasedPolicyLearning.samplingLaw_projectPolicySamples M N f, measureReal_def,
    Measure.map_apply (measurable_of_countable _) hmeas]
  convert hrisk using 1
  rw [measureReal_def]
  congr 2
  ext data
  simp only [Set.mem_preimage, Set.mem_setOf_eq, target]
  have hfun : QHat M.reward M.discount data - M.trajectoryExpectedQ M.optimalGreedyPolicy =
      ((fun s _ ↦ (VHat M.reward M.discount
        (ModelBasedPolicyLearning.projectPolicySamples N f data) -
          M.trajectoryExpectedValue (singleActionPolicy S)) s : Fin S → Fin 1 → ℝ)) := by
    funext s a
    simp only [Pi.sub_apply, QHat]
    rw [singleAction_trajectoryExpectedQ_eq]
  rw [hfun, norm_singleAction_lift]

end StatisticalRL.GenerativeLowerBound
