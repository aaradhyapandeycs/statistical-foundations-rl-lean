import Formalization.Generative.PolicyEvaluationHighSample
import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Convert the policy-evaluation API beta to the manuscript beta on the
multi-state branch. The one-state case is handled separately by
`valueEstimator_eq_true_of_subsingleton`. -/

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- At the exact source depth, the API beta is bounded by eight times the
manuscript logarithm when there are at least two states and `0 < δ < 1`. -/
theorem policyEvaluationBeta_le_eight_source_log
    (M : DiscountedMDP State Action) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hS : (2 : ℝ) ≤ (Fintype.card State : ℝ)) :
    policyEvaluationBeta M δ ≤
      8 * Real.log ((Fintype.card State : ℝ) *
        (policyEvaluationDepth M : ℝ) / δ) := by
  let h : ℝ := 1 - M.discount
  let S : ℝ := Fintype.card State
  let m : ℝ := policyEvaluationDepth M
  have hh : 0 < h := by
    dsimp [h]
    exact sub_pos.mpr M.discount_lt_one
  have hh1 : h ≤ 1 := by
    dsimp [h]
    linarith [M.discount_nonneg]
  have hS0 : 0 < S := by dsimp [S]; linarith
  have hmpos : 0 < policyEvaluationDepth M := by
    dsimp [policyEvaluationDepth]
    apply Nat.ceil_pos.mpr
    apply Real.log_pos
    apply (lt_div_iff₀ hh).2
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    simpa only [one_mul] using lt_of_le_of_lt hh1 hexp
  have hm1 : (1 : ℝ) ≤ m := by
    dsimp [m]
    exact_mod_cast hmpos
  have hδpos : 0 < δ := hδ
  have hx : 2 ≤ S * m / δ := by
    apply (le_div_iff₀ hδpos).2
    dsimp [S]
    nlinarith [hm1, hS]
  have hxpos : 0 < S * m / δ := by linarith
  have hmplus : m + 1 ≤ 2 * m := by nlinarith
  have hnum : 4 * S * (m + 1) ≤ 8 * S * m := by
    nlinarith [mul_nonneg (show 0 ≤ 4 * S by positivity)
      (sub_nonneg.mpr hmplus)]
  have harg : 4 * S * (m + 1) / δ ≤ 8 * (S * m / δ) := by
    calc
      4 * S * (m + 1) / δ ≤ (8 * S * m) / δ :=
        div_le_div_of_nonneg_right hnum hδpos.le
      _ = 8 * (S * m / δ) := by ring
  have hargpos : 0 < 4 * S * (m + 1) / δ := by positivity
  have hlogcmp : Real.log (4 * S * (m + 1) / δ) ≤
      4 * Real.log (S * m / δ) := by
    have hmono := Real.log_le_log hargpos harg
    have hmul : Real.log (8 * (S * m / δ)) =
        Real.log 8 + Real.log (S * m / δ) := by
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
        (ne_of_gt hxpos)]
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog2 : Real.log 2 ≤ Real.log (S * m / δ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    rw [hmul, hlog8] at hmono
    nlinarith
  have hbeta : policyEvaluationBeta M δ =
      2 * Real.log (4 * S * (m + 1) / δ) := by
    simp [policyEvaluationBeta, policyEvaluationDepth,
      auxiliaryRecursionLog, S, m]
  rw [hbeta]
  nlinarith [hlogcmp]

/-- Explicitly choose `C₀ ≥ 8`; then the API radius event is contained in
the manuscript-`β₁` radius event. This is the event transfer used to consume
the all-positive-sample API result. -/
theorem policyEvaluation_api_radius_event_subset_source_beta_radius
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (N : ℕ) (hN : 0 < N) (δ C₀ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hC₀ : 8 ≤ C₀)
    (hS : (2 : ℝ) ≤ (Fintype.card State : ℝ)) :
    {data : Samples State N |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 * policyEvaluationBeta M δ /
          ((1 - M.discount) ^ 3 * N))} ⊆
    {data : Samples State N |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 *
          (C₀ * Real.log ((Fintype.card State : ℝ) *
            (policyEvaluationDepth M : ℝ) / δ)) /
          ((1 - M.discount) ^ 3 * N))} := by
  intro data hdata
  change ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ _ at hdata
  change ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ _
  apply hdata.trans
  have hbeta := policyEvaluationBeta_le_eight_source_log M δ hδ hδ1 hS
  have hlog : 0 ≤ Real.log
      ((Fintype.card State : ℝ) * (policyEvaluationDepth M : ℝ) / δ) := by
    apply Real.log_nonneg
    have hmpos : 0 < policyEvaluationDepth M := by
      dsimp [policyEvaluationDepth]
      apply Nat.ceil_pos.mpr
      apply Real.log_pos
      have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
      apply (lt_div_iff₀ hh).2
      have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
      have hh1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
      simpa only [one_mul] using lt_of_le_of_lt hh1 hexp
    have harg : 1 ≤ (Fintype.card State : ℝ) *
        (policyEvaluationDepth M : ℝ) / δ := by
      apply (le_div_iff₀ hδ).2
      have hm1 : (1 : ℝ) ≤ (policyEvaluationDepth M : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmpos))
      nlinarith [hS]
    exact harg
  have hbeta' : policyEvaluationBeta M δ ≤
      C₀ * Real.log
        ((Fintype.card State : ℝ) * (policyEvaluationDepth M : ℝ) / δ) := by
    nlinarith
  have hden : 0 < (1 - M.discount) ^ 3 * (N : ℝ) := by
    have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hradarg := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbeta' (by norm_num : (0 : ℝ) ≤ 8)) hden.le
  have hsqrt := Real.sqrt_le_sqrt hradarg
  nlinarith

end StatisticalRL.ModelBasedPolicyEvaluation
