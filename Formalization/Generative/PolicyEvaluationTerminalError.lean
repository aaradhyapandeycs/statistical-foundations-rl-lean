import Formalization.Generative.PolicyEvaluationAuxiliaryGrowth
import Formalization.Generative.PolicyEvaluationAuxiliaryBernstein
import Formalization.Generative.PolicyEvaluationResidualRecursion
import Formalization.Generative.PolicyEvaluationEmpiricalResolvent

/-! Terminal auxiliary error from the actual inverse norm and residual bound.
The terminal estimate is proved, not supplied as an assumption. -/
open scoped Matrix
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance terminalStateDecidable : DecidableEq State := Classical.decEq State
local instance terminalStateMeasurable : MeasurableSpace State := ⊤

/-- Step 4 before geometric growth: the bounded residual and actual empirical
inverse give the terminal error directly, with no next-level error term. -/
theorem auxiliary_terminal_error_conditional (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (l : ℕ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hres : ∀ s,
      |((empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ
        auxiliaryValue M π l) s| ≤
      a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) +
        c * ‖auxiliaryValue M π l‖) :
    ‖empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l‖ ≤
      M.discount / (1 - M.discount) * (a + c) * ‖auxiliaryValue M π l‖ := by
  let z := (empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ auxiliaryValue M π l
  have hg (s : State) : Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) ≤
      ‖auxiliaryValue M π l‖ := by
    have hn := norm_le_pi_norm (auxiliaryReward M π (l + 1)) s
    change ‖Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l))‖ ≤ _ at hn
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
    exact hn.trans (auxiliaryReward_succ_norm_le M π l)
  have hz : ‖z‖ ≤ (a + c) * ‖auxiliaryValue M π l‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg ha hc) (norm_nonneg _))).2
    intro s
    rw [Real.norm_eq_abs]
    have hh := hres s
    have hm := mul_le_mul_of_nonneg_left (hg s) ha
    change |z s| ≤ _ at hh
    nlinarith only [hh, hm]
  have he := empirical_true_resolvent_norm_le M π N hN data (auxiliaryReward M π l)
  rw [auxiliaryValue_eq_inverse M π l] at he
  change ‖empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l‖ ≤
    M.discount / (1 - M.discount) * ‖z‖ at he
  have hcoeff : 0 ≤ M.discount / (1 - M.discount) :=
    div_nonneg M.discount_nonneg (sub_pos.mpr M.discount_lt_one).le
  exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hz hcoeff])

/-- The source's explicit terminal estimate after its geometric true-value bound. -/
theorem auxiliary_terminal_error_growth_conditional (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (m : ℕ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hγ : 0 < M.discount)
    (hres : ∀ s,
      |((empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ auxiliaryValue M π m) s| ≤
      a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π m)) +
        c * ‖auxiliaryValue M π m‖) :
    ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
      M.discount / (1 - M.discount) ^ 2 * (a + c) *
        (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ m := by
  have he := auxiliary_terminal_error_conditional M π N hN data m a c ha hc hres
  have hv := auxiliaryValue_norm_growth_source_uniform M π m hγ
  have hcoeff : 0 ≤ M.discount / (1 - M.discount) * (a + c) :=
    mul_nonneg (div_nonneg M.discount_nonneg (sub_pos.mpr M.discount_lt_one).le) (add_nonneg ha hc)
  calc
    _ ≤ M.discount / (1 - M.discount) * (a + c) * ‖auxiliaryValue M π m‖ := he
    _ ≤ M.discount / (1 - M.discount) * (a + c) *
        ((1 / (1 - M.discount)) *
          (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ m) :=
      mul_le_mul_of_nonneg_left hv hcoeff
    _ = _ := by simp only [div_eq_mul_inv, ← inv_pow]; ring

/-- The terminal contribution after unrolling, with its exact ratio preserved. -/
theorem auxiliary_terminal_contribution_conditional (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (m : ℕ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hγ : 0 < M.discount)
    (hres : ∀ s,
      |((empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ auxiliaryValue M π m) s| ≤
      a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π m)) +
        c * ‖auxiliaryValue M π m‖) :
    (M.discount * a) ^ m *
      ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
      (M.discount * a * (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount)))) ^ m *
        M.discount / (1 - M.discount) ^ 2 * (a + c) := by
  have he := auxiliary_terminal_error_growth_conditional M π N hN data m a c ha hc hγ hres
  have hp := mul_le_mul_of_nonneg_left he (pow_nonneg (mul_nonneg M.discount_nonneg ha) m)
  convert hp using 1
  rw [mul_pow]
  ring

/-- The genuine simultaneous Bernstein event supplies the terminal residual;
its exact linear 1/3 coefficient is retained in the resulting error bound. -/
theorem auxiliary_terminal_error_bernstein (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
      M.discount / (1 - M.discount) *
        (Real.sqrt (2 * Real.log (4 * Fintype.card State * (m + 1) / δ) / N) +
          2 * Real.log (4 * Fintype.card State * (m + 1) / δ) / (3 * N)) *
        ‖auxiliaryValue M π m‖} := by
  letI : Nonempty State := M.state_nonempty
  let μ := samplingLaw M π N
  let L := Real.log (4 * Fintype.card State * ((m : ℝ) + 1) / δ)
  let a := Real.sqrt (2 * L / N)
  let c := 2 * L / (3 * N)
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hp : (1 : ℝ) ≤ (Fintype.card State : ℝ) * ((m : ℝ) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hm)]
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).2 (by nlinarith))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let good : Set (Samples State N) := {data | ∀ (s : State) (l : Fin (m + 1)),
    |(empiricalPolicyRow N hN data s).expectation (auxiliaryValue M π l) -
      (M.policyTransition π s).expectation (auxiliaryValue M π l)| ≤
    a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) +
      2 * ‖auxiliaryValue M π l‖ * L / (3 * N)}
  have hs : 1 - δ < μ.real good := auxiliaryValues_bernstein_explicit M π N hN m δ hδ hδ1
  let target : Set (Samples State N) := {data |
    ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
      M.discount / (1 - M.discount) * (a + c) * ‖auxiliaryValue M π m‖}
  have hsub : good ⊆ target := by
    intro data hd
    apply auxiliary_terminal_error_conditional M π N hN data m a c ha hc
    intro s
    simp only [Matrix.sub_mulVec, Pi.sub_apply, empiricalMatrix_mulVec, evaluationPolicyMatrix_mulVec]
    have hh := hd s ⟨m, Nat.lt_succ_self m⟩
    convert hh using 1
    dsimp [c]
    ring
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

/-- Actual-law raw weighted terminal contribution, prior to numerical decay
and without an assumed terminal-error event. -/
theorem auxiliary_terminal_contribution_bernstein (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < M.discount) :
    let L := Real.log (4 * Fintype.card State * ((m : ℝ) + 1) / δ)
    let a := Real.sqrt (2 * L / N)
    let c := 2 * L / (3 * N)
    let b := Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))
    1 - δ < (samplingLaw M π N).real {data |
      (M.discount * a) ^ m *
        ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
      (M.discount * a * b) ^ m * M.discount / (1 - M.discount) ^ 2 * (a + c)} := by
  letI : Nonempty State := M.state_nonempty
  let μ := samplingLaw M π N
  let L := Real.log (4 * Fintype.card State * ((m : ℝ) + 1) / δ)
  let a := Real.sqrt (2 * L / N)
  let c := 2 * L / (3 * N)
  let b := Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hp : (1 : ℝ) ≤ (Fintype.card State : ℝ) * ((m : ℝ) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hm)]
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).2 (by nlinarith))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let good : Set (Samples State N) := {data |
    ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
      M.discount / (1 - M.discount) * (a + c) * ‖auxiliaryValue M π m‖}
  have hs : 1 - δ < μ.real good := auxiliary_terminal_error_bernstein M π N hN m δ hδ hδ1
  let target : Set (Samples State N) := {data |
    (M.discount * a) ^ m *
      ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
    (M.discount * a * b) ^ m * M.discount / (1 - M.discount) ^ 2 * (a + c)}
  have hsub : good ⊆ target := by
    intro data hd
    have hv := auxiliaryValue_norm_growth_source_uniform M π m hγ
    have hcoeff : 0 ≤ M.discount / (1 - M.discount) * (a + c) :=
      mul_nonneg (div_nonneg M.discount_nonneg (sub_pos.mpr M.discount_lt_one).le) (add_nonneg ha hc)
    have he : ‖empiricalAuxiliaryValue M π N hN data m - auxiliaryValue M π m‖ ≤
        M.discount / (1 - M.discount) ^ 2 * (a + c) * b ^ m := by
      calc
        _ ≤ M.discount / (1 - M.discount) * (a + c) * ‖auxiliaryValue M π m‖ := hd
        _ ≤ M.discount / (1 - M.discount) * (a + c) *
            ((1 / (1 - M.discount)) * b ^ m) := mul_le_mul_of_nonneg_left hv hcoeff
        _ = _ := by simp only [div_eq_mul_inv, ← inv_pow]; ring
    have hw := mul_le_mul_of_nonneg_left he (pow_nonneg (mul_nonneg M.discount_nonneg ha) m)
    dsimp only [target, Set.mem_setOf_eq]
    convert hw using 1
    rw [mul_pow]
    ring
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyEvaluation
