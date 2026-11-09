import Formalization.ModelFree.QLearningUnderestimationCoupling
import Formalization.ModelFree.QLearningUnderestimationLaw
import Formalization.ModelFree.QLearningUnderestimationValue
import Formalization.ModelFree.TDLogCubeUnitConstants

/-! assembly of the under-estimation bound after Theorem 4.6
(`chapters/generative_model_model_free.tex:1869–1881`). -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
open StatisticalRL.TemporalDifference
universe u v

/-- Rates admissible for the log³ schedule with `c₁ = 1` lie in `[0,1]`. -/
theorem qLogCubeUnitSchedule_unit (γ : ℝ) (hγ : γ < 1) (T : ℕ) (hT : 2 ≤ T) (η : ℕ → ℝ)
    (hη : ∀ k, k ≤ T →
      1 / (1 + 1 * (1 - γ) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
      η k ≤ 1 / (1 + 1 * (1 - γ) * k / Real.log (T : ℝ) ^ 3))
    (k : ℕ) (hk : k ≤ T) : 0 ≤ η k ∧ η k ≤ 1 := by
  have hgap : 0 ≤ 1 - γ := by linarith
  have hL : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  obtain ⟨hlo, hhi⟩ := hη k hk
  have hx : 0 ≤ 1 * (1 - γ) * (T : ℝ) / Real.log (T : ℝ) ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_one hgap) (Nat.cast_nonneg _))
      (pow_nonneg hL.le 3)
  have hy : 0 ≤ 1 * (1 - γ) * (k : ℝ) / Real.log (T : ℝ) ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_one hgap) (Nat.cast_nonneg _))
      (pow_nonneg hL.le 3)
  constructor
  · exact le_trans (div_nonneg zero_le_one (by linarith)) hlo
  · refine hhi.trans ?_
    rw [div_le_one (by linarith)]
    linarith

/-- Under-estimation bound for synchronous Q-learning (prose claim after Theorem 4.6,
`chapters/generative_model_model_free.tex:1869–1881`), with witnesses `c₁ = c₂ = 1`,
`C = 91`. Clause 1 is pathwise; clause 2 holds with probability at least `1 − δ`
simultaneously for all `(s,a)`, for every `T ≥ 2`. -/
theorem qLearning_underestimation_exists_universal_constants :
    ∃ c₁ c₂ C : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < C ∧
    ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount → 2 ≤ T → 0 < δ → δ < 1 →
      (∀ k, k ≤ T →
        1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
        η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
      ∀ (Q₀ : State → Action → ℝ), (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      ∀ (f : State → Action),
        (∀ s, M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s =
          M.trajectoryExpectedValue M.optimalGreedyPolicy s) →
      (∀ (data : QSamples State Action T) s a,
          qPolicySampledIterate M f η T Q₀ data s a ≤ qSampledIterate M η T Q₀ data s a) ∧
      1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
        -(C * Real.sqrt (Real.log (T : ℝ) ^ 4 *
            Real.log ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) /
            ((1 - M.discount) ^ 3 * T))) ≤
          qPolicySampledIterate M f η T Q₀ data s a -
            M.trajectoryExpectedQ M.optimalGreedyPolicy s a} := by
  refine ⟨1, 1, 91, one_pos, le_rfl, by norm_num, ?_⟩
  intro State Action _ _ M η δ T hγ hT hδ hδ1 hη Q₀ h₀ f hf
  have hunit := qLogCubeUnitSchedule_unit M.discount M.discount_lt_one T hT η hη
  have hη1 : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1 := fun k _ hk ↦ hunit k hk
  refine ⟨fun data s a ↦
    qPolicyEvaluationIterate_le_qLearningIterate M f η _ Q₀ T hη1 s a, ?_⟩
  -- constants of the bound
  set L : ℝ := Real.log (T : ℝ) with hLdef
  set ℓ : ℝ := Real.log ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ)
    with hℓdef
  set X : ℝ := L ^ 4 * ℓ / ((1 - M.discount) ^ 3 * T) with hXdef
  set ε : ℝ := Real.sqrt (8192 * X) with hεdef
  have hgap : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hL : 0 < L := Real.log_pos (by linarith)
  have hS : (1 : ℝ) ≤ Fintype.card State := by
    exact_mod_cast Fintype.card_pos_iff.mpr M.state_nonempty
  have hA : (1 : ℝ) ≤ Fintype.card Action := by
    exact_mod_cast Fintype.card_pos_iff.mpr M.action_nonempty
  have hSAT : (2 : ℝ) ≤ (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T := by
    have h1 : (1 : ℝ) ≤ (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) :=
      one_le_mul_of_one_le_of_one_le hS hA
    nlinarith
  have hℓ : 0 < ℓ := Real.log_pos ((one_lt_div hδ).mpr (by linarith))
  have hX : 0 < X := by positivity
  have hεpos : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hεC : ε ≤ 91 * Real.sqrt X := by
    have h91 : (91 : ℝ) = Real.sqrt (91 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [h91, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  set E : Set (QSamples State Action T) := {data | ∀ s a,
    -(91 * Real.sqrt X) ≤ qPolicySampledIterate M f η T Q₀ data s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a} with hEdef
  change 1 - δ ≤ (qSamplingLaw M T).real E
  by_cases hcase : ε ≤ M.effectiveHorizon
  · -- the transported TD bound applies with ε at equality in the budget
    let M' := qPolicyLiftMDP M f
    let Q₀' : State × Action → ℝ := fun y ↦ Q₀ y.1 y.2
    have hcard : ((Fintype.card (State × Action) : ℕ) : ℝ) =
        (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) := by
      rw [Fintype.card_prod, Nat.cast_mul]
    have hε2 : ε ^ 2 = 8192 * X := Real.sq_sqrt (by positivity)
    have hbudget : 8192 * Real.log (T : ℝ) ^ 4 *
        Real.log ((Fintype.card (State × Action) : ℝ) * T / δ) /
          ((1 - M'.discount) ^ 3 * ε ^ 2) ≤ T := by
      change 8192 * L ^ 4 * Real.log ((Fintype.card (State × Action) : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ T
      rw [hcard, ← hℓdef, hε2, hXdef]
      apply le_of_eq
      have hT0 : (T : ℝ) ≠ 0 := by positivity
      have hg3 : (1 - M.discount) ^ 3 ≠ 0 := by positivity
      field_simp
    have hTD := tdSource_logCube_unitConstants_exactSamples_accuracy M' qPolicyLiftPolicy
      η δ ε T hγ hT hδ hδ1 hεpos hcase (fun i _ hi ↦ hη i hi) Q₀'
      (fun y ↦ h₀ y.1 y.2) hbudget
    refine hTD.trans ?_
    rw [← qSamplingLaw_real_preimage_qPolicyLiftData]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro data hd s a
    have hx := hd (s, a)
    change |tdSourceSampledIterate M' qPolicyLiftPolicy η T Q₀' (qPolicyLiftData f data)
      (s, a) - M'.trajectoryExpectedValue qPolicyLiftPolicy (s, a)| ≤ ε at hx
    rw [tdSourceSampledIterate_qPolicyLift, qPolicyLift_trajectoryExpectedValue_optimal M f hf]
      at hx
    have := (abs_le.mp hx).1
    change -(91 * Real.sqrt X) ≤ _
    linarith
  · -- the bound is below the trivial range: the event is the whole sample space
    have hall : E = Set.univ := by
      apply Set.eq_univ_of_forall
      intro data s a
      have hnn := qPolicyEvaluationIterate_nonneg M f η (qSamplesExtend M T data) Q₀
        (fun s a ↦ (h₀ s a).1) T hη1 s a
      have hQ := (M.trajectoryExpectedQ_bounds M.optimalGreedyPolicy s a).2
      have hH : M.effectiveHorizon = 1 / (1 - M.discount) := rfl
      change -(91 * Real.sqrt X) ≤ qPolicyEvaluationIterate M f η (qSamplesExtend M T data)
        Q₀ T s a - M.trajectoryExpectedQ M.optimalGreedyPolicy s a
      push_neg at hcase
      rw [hH] at hcase
      linarith
    rw [hall, probReal_univ]
    linarith

end StatisticalRL.QLearning
