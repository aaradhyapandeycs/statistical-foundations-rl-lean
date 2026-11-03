import Formalization.Generative.PolicyLearningSourcePointwise
import Formalization.Generative.PolicyLearningMainSampleArithmetic

/-! Source main-theorem candidate: singleton exactness and main sample budget. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mainSampleStateMeasurable : MeasurableSpace State := ⊤

/-- On a one-state MDP all projected policy-evaluation estimators are exact. -/
theorem singletonState_empirical_policy_value_exact [Subsingleton State]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (f : State → Action) :
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) =
    M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) := by
  rw [projectedPolicy_value_eq]
  exact ModelBasedPolicyEvaluation.valueEstimator_eq_true_of_subsingleton M _ N hN _

/-- Every empirical-optimal tie policy is truly optimal on a one-state MDP. -/
theorem singletonState_empirical_optimal_exact [Subsingleton State]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (f : State → Action)
    (hf : EmpiricallyOptimal M N hN data f) :
    (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s =
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
    (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a =
      M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a) := by
  have h₀ : ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ 0 := by
    rw [show M.optimalGreedyPolicy = (fun t ↦ EnvironmentStage.pointMass (M.optimalGreedyAction t)) from rfl,
      singletonState_empirical_policy_value_exact, sub_self, norm_zero]
  have h₁ : ‖(empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t)) -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 0 := by
    rw [singletonState_empirical_policy_value_exact, sub_self, norm_zero]
  have hs := empiricallyOptimal_performance M N hN data f hf 0 0 h₀ h₁
  constructor
  · intro s
    have h := hs.1 s
    linarith
  · intro s a
    have h := hs.2 s a
    simp only [add_zero, mul_zero] at h
    linarith

/-- The printed N-dependent budget yields the source V and Q performance
bounds simultaneously for all empirical-optimal deterministic policies. -/
theorem mainSample_policyLearning (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - M.discount))
    (hbudget : 10240 * Real.log (Fintype.card State * Fintype.card Action * N /
      ((1 - M.discount) ^ 2 * ε * δ)) / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ < (samplingLaw M N).real {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
        (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a - M.discount * ε ≤
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a)} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let h := 1 - M.discount
  let β := leaveOneOutBeta M N δ
  let L := Real.log (Fintype.card State * Fintype.card Action * N / (h ^ 2 * ε * δ))
  let q := Real.sqrt (β / (N * h ^ 3))
  let target : Set (Samples State Action N) := {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
        (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a - M.discount * ε ≤
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a)}
  by_cases hs : Fintype.card State ≤ 1
  · letI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hs
    have ht : target = Set.univ := by
      ext data
      simp only [Set.mem_univ, iff_true]
      intro f hf
      have he := singletonState_empirical_optimal_exact M N hN data f hf
      constructor
      · intro s
        rw [he.1 s]
        linarith
      · intro s a
        rw [he.2 s a]
        have : 0 ≤ M.discount * ε := mul_nonneg M.discount_nonneg hε.le
        linarith
    change 1 - δ < (samplingLaw M N).real target
    rw [ht, probReal_univ]
    linarith
  · have hS : (2 : ℝ) ≤ Fintype.card State := by
      have hSn : 2 ≤ Fintype.card State := by omega
      exact_mod_cast hSn
    have hA : (1 : ℝ) ≤ Fintype.card Action := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hK : 2 ≤ (Fintype.card State : ℝ) * Fintype.card Action * N := by
      have hSA : 2 ≤ (Fintype.card State : ℝ) * Fintype.card Action := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ (Fintype.card State : ℝ) by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (show 0 ≤ (Fintype.card State : ℝ) * Fintype.card Action by positivity)]
    have hh : 0 < h := sub_pos.mpr M.discount_lt_one
    have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
    have hlog := mainSample_log_comparison h ε δ
      ((Fintype.card State : ℝ) * Fintype.card Action * N) hh hh1 hε hδ hδ1 hεmax hK
    have hβL : β ≤ 10 * L := by
      dsimp [β, L, leaveOneOutBeta]
      convert hlog using 1 <;> congr 2 <;> ring
    have hβ : 0 ≤ β := le_trans (by norm_num) (leaveOneOutBeta_ge_four M N hN δ hδ hδ1)
    have hb : 10240 * L / (h ^ 3 * ε ^ 2) ≤ N := hbudget
    have hmain := mainSample_scalar_bounds h ε β L N hh hε hεmax hβ hβL hb
    have hcut : 720 * β / h ≤ N := hmain.1
    have herr : 32 * q ≤ ε := hmain.2
    let good : Set (Samples State Action N) := {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
          16 * Real.sqrt (2 * β / (N * h ^ 3)) ∧
        ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ 2 * 16 * q ∧
        ∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
          M.trajectoryExpectedValue M.optimalGreedyPolicy s -
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ 2 * 16 * q}
    have hp : 1 - δ < (samplingLaw M N).real good :=
      source_policyLearning_evaluation_with_pointwise M N hN δ hδ hδ1 hcut
    change 1 - δ < (samplingLaw M N).real target
    apply hp.trans_le
    apply measureReal_mono _ (measure_ne_top (samplingLaw M N) target)
    intro data hd f hf
    have hv (s : State) : M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ ε := by
      have hh' := ((hd f hf).2.2 s).2
      linarith
    constructor
    · intro s
      linarith [hv s]
    · intro s a
      have hq := M.trajectoryQ_loss_le_discount_of_value_loss _ ε hv s a
      linarith [hq.2]

/-- One explicit universal constant precedes every finite model and accuracy;
positive N is the sampling/log-domain condition. -/
theorem mainSample_policyLearning_universal_constant :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ ε : ℝ),
      0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
      c₀ * Real.log (Fintype.card State * Fintype.card Action * N /
        ((1 - M.discount) ^ 2 * ε * δ)) / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
      1 - δ < (samplingLaw M N).real {data |
        ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
          (∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s - ε ≤
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s) ∧
          (∀ s a, M.trajectoryExpectedQ M.optimalGreedyPolicy s a - M.discount * ε ≤
            M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a)} := by
  refine ⟨10240, by norm_num, ?_⟩
  intro State Action _ _ M N hN δ ε hδ hδ1 hε hεmax hbudget
  exact mainSample_policyLearning M N hN δ ε hδ hδ1 hε hεmax hbudget

end StatisticalRL.ModelBasedPolicyLearning
