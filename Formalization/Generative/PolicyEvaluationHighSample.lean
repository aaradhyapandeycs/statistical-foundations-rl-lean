import Formalization.Generative.PolicyEvaluationBernsteinRecursion
import Formalization.Generative.PolicyEvaluationAuxiliaryGrowth
import Formalization.Generative.PolicyEvaluationFinalArithmetic
import Formalization.Generative.PolicyEvaluationTerminalError

/-! Actual-law high-sample assembly with explicit depth and confidence radius.
The single simultaneous residual event supplies both recursion and terminal
control, so no independence/intersection of separately proved events is used. -/
open scoped Matrix
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance highSampleStateDecidable : DecidableEq State := Classical.decEq State
local instance highSampleStateMeasurable : MeasurableSpace State := ⊤

noncomputable def policyEvaluationDepth (M : DiscountedMDP State Action) : ℕ :=
  ⌈Real.log (Real.exp 1 / (1 - M.discount))⌉₊

noncomputable def policyEvaluationBeta (M : DiscountedMDP State Action) (δ : ℝ) : ℝ :=
  2 * auxiliaryRecursionLog (State := State) (policyEvaluationDepth M) δ

/-- Positive-discount high-sample bound at the exact displayed source radius.
All recurrence, growth and terminal inputs are supplied on one real event. -/
theorem valueEstimator_high_sample_of_pos (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < M.discount)
    (hNbound : 64 * policyEvaluationBeta M δ / (1 - M.discount) ≤ N) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 * policyEvaluationBeta M δ / ((1 - M.discount) ^ 3 * N))} := by
  let μ := samplingLaw M π N
  let h := 1 - M.discount
  let m := policyEvaluationDepth M
  let L := auxiliaryRecursionLog (State := State) m δ
  let β := policyEvaluationBeta M δ
  let a := Real.sqrt (β / N)
  let c := β / N
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
  have hL : 0 < L := auxiliaryRecursionLog_pos M m δ hδ hδ1
  have hβ : 0 ≤ β := by change 0 ≤ 2 * L; positivity
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := div_nonneg hβ hn.le
  have hm : -Real.log h ≤ (m : ℝ) := auxiliary_source_ceiling_depth h hh
  let good : Set (Samples State N) := {data | ∀ (s : State) (l : Fin (m + 1)),
    |(empiricalPolicyRow N hN data s).expectation (auxiliaryValue M π l) -
      (M.policyTransition π s).expectation (auxiliaryValue M π l)| ≤
    a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) +
      2 * ‖auxiliaryValue M π l‖ * L / (3 * N)}
  have hs : 1 - δ < μ.real good := auxiliaryValues_bernstein_explicit M π N hN m δ hδ hδ1
  let target : Set (Samples State N) := {data |
    ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
      3 * Real.sqrt (8 * β / (h ^ 3 * N))}
  have hsub : good ⊆ target := by
    intro data hd
    let E : ℕ → ℝ := fun l ↦ ‖empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l‖
    let V : ℕ → ℝ := fun l ↦ ‖auxiliaryValue M π l‖
    have hres (l : ℕ) (hl : l ≤ m) (s : State) :
        |((empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ auxiliaryValue M π l) s| ≤
        a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) + c * V l := by
      simp only [Matrix.sub_mulVec, Pi.sub_apply, empiricalMatrix_mulVec, evaluationPolicyMatrix_mulVec]
      have hhres := hd s ⟨l, Nat.lt_succ_of_le hl⟩
      have hlinear : 2 * ‖auxiliaryValue M π l‖ * L / (3 * N) ≤ c * V l := by
        have hnon : 0 ≤ c * V l := mul_nonneg hc (norm_nonneg _)
        have heq : 2 * ‖auxiliaryValue M π l‖ * L / (3 * N) = (c * V l) / 3 := by
          dsimp [c, β, policyEvaluationBeta, L, m, V]
          ring
        rw [heq]
        linarith
      exact hhres.trans (add_le_add le_rfl hlinear)
    have hstep (l : ℕ) (hl : l < m) : E l ≤ M.discount * a * E (l + 1) +
        (Real.sqrt 2 * a / Real.sqrt h + (β / N) / h) * V l := by
      have hr := auxiliary_residual_recursion_conditional M π N hN data l a c ha hc
        (hres l (Nat.le_of_lt hl))
      have hg := auxiliaryValue_succ_scaled_bound M π l
      have hnext : M.discount * a * V (l + 1) ≤ Real.sqrt 2 * a / Real.sqrt h * V l := by
        have hmult := mul_le_mul_of_nonneg_left hg ha
        have hk : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
        have hnon : 0 ≤ a * V l / Real.sqrt h := by positivity
        have hextra := mul_le_mul_of_nonneg_right hk hnon
        change M.discount * a * ‖auxiliaryValue M π (l + 1)‖ ≤ _
        dsimp [V, h] at hextra ⊢
        simp only [div_eq_mul_inv] at hmult hextra ⊢
        nlinarith only [hmult, hextra]
      have hlinear : M.discount * c * V l / h ≤ (β / N) / h * V l := by
        have hnon : 0 ≤ c * V l / h := by positivity
        have hh := mul_le_mul_of_nonneg_right M.discount_lt_one.le hnon
        dsimp [c] at hh ⊢
        simp only [div_eq_mul_inv] at hh ⊢
        nlinarith only [hh]
      change E l ≤ M.discount * a * (E (l + 1) + V (l + 1)) + M.discount * c * V l / h at hr
      simp only [div_eq_mul_inv] at hr hnext hlinear ⊢
      nlinarith only [hr, hnext, hlinear]
    have hvalue (l : ℕ) (_hl : l ≤ m) : V l ≤
        (Real.sqrt 2 / (M.discount * Real.sqrt h)) ^ l * V 0 := by
      exact auxiliaryValue_norm_growth_source M π l hγ
    have hterminal : E m ≤ M.discount / h * (a + β / N) * V m :=
      auxiliary_terminal_error_conditional M π N hN data m a c ha hc (hres m le_rfl)
    have hV0 : 0 ≤ V 0 := norm_nonneg _
    have hVB : V 0 ≤ 1 / h := ModelBasedPolicyEvaluation.truePolicyValue_norm_bound M π
    have hfinal := auxiliary_source_high_sample_radius E V M.discount h β N m
      hγ M.discount_lt_one.le hh hh1 hβ hn hNbound hm hV0 hVB hstep hvalue hterminal
    change E 0 ≤ _ at hfinal
    simpa only [E, empiricalAuxiliaryValue_zero, auxiliaryValue] using hfinal
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

/-- The same high-sample conclusion on the full source discount domain;
zero discount is exact for every sample and is handled separately. -/
theorem valueEstimator_high_sample (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hNbound : 64 * policyEvaluationBeta M δ / (1 - M.discount) ≤ N) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 * policyEvaluationBeta M δ / ((1 - M.discount) ^ 3 * N))} := by
  by_cases hp : 0 < M.discount
  · exact valueEstimator_high_sample_of_pos M π N hN δ hδ hδ1 hp hNbound
  · have hz : M.discount = 0 := le_antisymm (not_lt.mp hp) M.discount_nonneg
    have heq : {data : Samples State N |
        ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
          3 * Real.sqrt (8 * policyEvaluationBeta M δ / ((1 - M.discount) ^ 3 * N))} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have he := auxiliaryValue_empirical_eq_of_zero M π N hN data 0 hz
      rw [empiricalAuxiliaryValue_zero] at he
      change valueEstimator M π N hN data = M.trajectoryExpectedValue π at he
      rw [he, sub_self, norm_zero]
      positivity
    rw [heq, probReal_univ]
    linarith

end StatisticalRL.ModelBasedPolicyEvaluation
