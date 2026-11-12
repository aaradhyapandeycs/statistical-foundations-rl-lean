import Formalization.Generative.PolicyLearningFixedPolicyProjection
import Formalization.Generative.PolicyLearningAnyOptimalPolicy

/-! Joint fixed- and fitted-policy evaluation on the same actual experiment. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance jointEvaluationStateMeasurable : MeasurableSpace State := ⊤

/-- The fixed-policy source logarithm is bounded by the learning β. -/
theorem fixedPolicy_log_le_beta (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log (Fintype.card State / ((δ / 2) * (1 - M.discount))) ≤
      leaveOneOutBeta M N δ := by
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let h := 1 - M.discount
  have hS : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
  have ha : 0 < S / ((δ / 2) * h) := by positivity
  have ha1 : 1 ≤ S / ((δ / 2) * h) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hh1) hδ.le]
  have hb : S / ((δ / 2) * h) ≤ 16 * S * A * N / (h * δ) := by
    have hAN : 1 ≤ A * N := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hN1)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod := mul_nonneg (sub_nonneg.mpr hAN) (show 0 ≤ S * h * δ by positivity)
    have hprod' : S * h * δ ≤ S * h * δ * (A * N) := by nlinarith [hprod]
    calc
      S * (h * δ) ≤ S * h * δ * (A * N) := by linarith [hprod']
      _ ≤ 16 * S * A * N * (δ / 2 * h) := by
        have hp : 0 ≤ S * h * δ * (A * N) := by positivity
        nlinarith [hp]
  have hl : 0 ≤ Real.log (S / ((δ / 2) * h)) := Real.log_nonneg ha1
  have hm := Real.log_le_log ha hb
  change Real.log (S / ((δ / 2) * h)) ≤ 2 * Real.log (16 * S * A * N / (h * δ))
  linarith

/-- Explicit source-budget specialization, retaining the fixed-policy radius. -/
theorem trueOptimalPolicy_beta_event (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlarge : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
        M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤
      Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))} := by
  let h := 1 - M.discount
  let β := leaveOneOutBeta M N δ
  let r := Real.sqrt (720 * β / (N * h ^ 3))
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hb : 0 < β := lt_of_lt_of_le (by norm_num) (leaveOneOutBeta_ge_four M N hN δ hδ hδ1)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 720 * β / (N * h ^ 3) := Real.sq_sqrt (by positivity)
  have hmax : r ≤ 1 / h := by
    have hsq : r ^ 2 ≤ (1 / h) ^ 2 := by
      rw [hr2]
      have hl : 720 * β ≤ N * h := (div_le_iff₀ hh).1 hlarge
      apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) * h ^ 3)).2
      field_simp
      nlinarith
    have hi : 0 < 1 / h := by positivity
    nlinarith
  have hlog := fixedPolicy_log_le_beta M N hN δ hδ hδ1
  change Real.log (Fintype.card State / ((δ / 2) * h)) ≤ β at hlog
  have hlog' : Real.log (Fintype.card State * 2 / (δ * h)) ≤ β := by
    convert hlog using 1 <;> congr 1 <;> field_simp
  have hbudget : 720 * Real.log (Fintype.card State / ((δ / 2) * h)) /
      (h ^ 3 * r ^ 2) ≤ N := by
    rw [hr2]
    apply (div_le_iff₀ (by positivity : 0 < h ^ 3 * (720 * β / (N * h ^ 3)))).2
    field_simp
    nlinarith [hlog']
  exact trueOptimalPolicy_evaluation_event M N hN δ r hδ hδ1 hr hmax hbudget

/-- Conservative explicit common coefficient: √720 ≤ 27 and the fitted
bound ≤ 5 times the shared square-root scale. -/
theorem sourceEvaluation_radius_le (x h : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hsmall : x * h ^ 2 ≤ 1 / 16) :
    Real.sqrt (720 * x) ≤ 27 * Real.sqrt x ∧
    2 * Real.sqrt (2 * x) + 6 * (x * h) ≤ 5 * Real.sqrt x := by
  let q := Real.sqrt x
  let u := Real.sqrt (720 * x)
  let v := Real.sqrt (2 * x)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = x := Real.sq_sqrt hx
  have hu2 : u ^ 2 = 720 * x := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
  have hxh : 0 ≤ x * h := mul_nonneg hx hh
  have hs : (x * h) ^ 2 ≤ x / 16 := by
    have hm := mul_le_mul_of_nonneg_left hsmall hx
    nlinarith
  constructor
  · change u ≤ 27 * q
    nlinarith
  · change 2 * v + 6 * (x * h) ≤ 5 * q
    have hvq : 2 * v ≤ 3 * q := by nlinarith
    have hxq : 4 * (x * h) ≤ q := by nlinarith
    linarith

/-- The source sample threshold supplies the scalar condition used above. -/
theorem sourceEvaluation_concrete_radius_bounds (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlarge : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N) :
    Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ≤
      27 * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
    2 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
      6 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 2) ≤
      5 * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by
  let h := 1 - M.discount
  let β := leaveOneOutBeta M N δ
  let x := β / (N * h ^ 3)
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hb : 0 ≤ β := le_trans (by norm_num) (leaveOneOutBeta_ge_four M N hN δ hδ hδ1)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hl : 720 * β ≤ N * h := (div_le_iff₀ hh).1 hlarge
  have hs : x * h ^ 2 ≤ 1 / 16 := by
    dsimp [x]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) * h ^ 3)).2
    have hm := mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg h)
    nlinarith
  have hhbound := sourceEvaluation_radius_le x h hx hh.le hs
  convert hhbound using 1 <;> dsimp [x, h, β] <;> congr 2 <;> field_simp

/-- Both actual evaluation budgets and their deterministic V/Q consequences
hold simultaneously for every empirical-optimal deterministic tie choice. -/
theorem joint_policyEvaluation_event (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlarge : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N) :
    1 - δ < (samplingLaw M N).real {data |
      let r₀ := Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
      let r₁ := 2 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
        6 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 2)
      ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
        M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ r₀ ∧
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ r₁ ∧
        (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
          M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ r₀ + r₁) ∧
        (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ≤
            M.discount * (r₀ + r₁))} := by
  let μ := samplingLaw M N
  let r₀ := Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
  let r₁ := 2 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
        6 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 2)
  let A : Set (Samples State Action N) := {data |
    ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ r₀}
  let B : Set (Samples State Action N) := {data |
    ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
      ‖valueEstimator M N hN data - M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ r₁}
  have ha : 1 - δ / 2 < μ.real A := trueOptimalPolicy_beta_event M N hN δ hδ hδ1 hlarge
  have hb : 1 - δ / 2 < μ.real B := all_empiricallyOptimal_evaluation_source_bound M N hN δ hδ hδ1
  have hca := measureReal_compl (μ := μ) ((Set.to_countable A).measurableSet)
  have hcb := measureReal_compl (μ := μ) ((Set.to_countable B).measurableSet)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (Aᶜ ∪ Bᶜ)).measurableSet)
  rw [probReal_univ] at hca hcb hc
  have hu := measureReal_union_le (μ := μ) Aᶜ Bᶜ
  have hi : 1 - δ < μ.real (A ∩ B) := by
    have : (Aᶜ ∪ Bᶜ)ᶜ = A ∩ B := by ext x; simp
    rw [this] at hc
    linarith
  apply hi.trans_le
  apply measureReal_mono _ (measure_ne_top μ _)
  intro data hd
  refine ⟨hd.1, ?_⟩
  intro f hf
  have he := empiricallyOptimal_value_eq M N hN data f hf
  have h₁ : ‖(empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ r₁ := by
    rw [he]
    exact hd.2 f hf
  exact ⟨h₁, empiricallyOptimal_performance M N hN data f hf r₀ r₁ hd.1 h₁⟩

/-- Source-shaped simultaneous V bounds, with concrete shared constants
c₀ = 720 and c₁ = 16, uniformly over all exact empirical optimizers. -/
theorem source_policyLearning_evaluation_constants (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlarge : 720 * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N) :
    1 - δ < (samplingLaw M N).real {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
          16 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
        ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
          2 * 16 * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))} := by
  let q := Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
  let r₀ := Real.sqrt (720 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))
  let r₁ := 2 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
    6 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 2)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hb : 0 ≤ leaveOneOutBeta M N δ :=
    le_trans (by norm_num) (leaveOneOutBeta_ge_four M N hN δ hδ hδ1)
  have hroot : q ≤ Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by
    apply Real.sqrt_le_sqrt
    have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hx : 0 ≤ leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3) := by positivity
    have heq : 2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3) =
        2 * (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by ring
    rw [heq]
    linarith
  have hr := sourceEvaluation_concrete_radius_bounds M N hN δ hδ hδ1 hlarge
  change r₀ ≤ 27 * q ∧ r₁ ≤ 5 * q at hr
  have hfitted : r₁ ≤ 16 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) := by linarith
  have hsum : r₀ + r₁ ≤ 2 * 16 * q := by linarith [hr.1, hr.2]
  let good : Set (Samples State Action N) := {data |
      ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
        M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ r₀ ∧
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
        ‖(empiricalModel M N hN data).trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (f t)) -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ r₁ ∧
        (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
          M.trajectoryExpectedValue M.optimalGreedyPolicy s -
          M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ r₀ + r₁) ∧
        (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
          M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ≤ M.discount * (r₀ + r₁))}
  have hp : 1 - δ < (samplingLaw M N).real good := joint_policyEvaluation_event M N hN δ hδ hδ1 hlarge
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top (samplingLaw M N) _)
  intro data hd f hf
  obtain ⟨he, hv, _⟩ := hd.2 f hf
  refine ⟨he.trans hfitted, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (hv s).1] using (hv s).2.trans hsum

/-- A single pair of constants works uniformly over all finite MDPs, sample
counts, confidence parameters, and empirical-optimal deterministic policies. -/
theorem source_policyLearning_evaluation_universal_constants :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) (δ : ℝ),
      0 < δ → δ < 1 → c₀ * leaveOneOutBeta M N δ / (1 - M.discount) ≤ N →
      1 - δ < (samplingLaw M N).real {data |
        ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
          ‖(empiricalModel M N hN data).trajectoryExpectedValue
            (fun t ↦ EnvironmentStage.pointMass (f t)) -
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
            c₁ * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) ∧
          ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
            M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
            2 * c₁ * Real.sqrt (leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3))} := by
  refine ⟨720, 16, by norm_num, by norm_num, ?_⟩
  intro State Action _ _ M N hN δ hδ hδ1 hlarge
  exact source_policyLearning_evaluation_constants M N hN δ hδ hδ1 hlarge

end StatisticalRL.ModelBasedPolicyLearning
