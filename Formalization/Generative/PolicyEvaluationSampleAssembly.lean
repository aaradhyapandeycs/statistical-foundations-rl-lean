import Formalization.Generative.PolicyEvaluationHoeffding

/-! Source policy-evaluation sample-size assembly: deterministic arithmetic and
one-state exactness only; no final probability theorem is claimed here. -/

open scoped BigOperators

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- With one state, all empirical and true transition rows agree on the
true value, so the actual estimator is exact for every data realization. -/
theorem valueEstimator_eq_true_of_subsingleton [Subsingleton State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    valueEstimator M π N hN data = M.trajectoryExpectedValue π := by
  have hres (s : State) :
      |(empiricalPolicyRow N hN data s).expectation (M.trajectoryExpectedValue π) -
        (M.policyTransition π s).expectation (M.trajectoryExpectedValue π)| ≤ 0 := by
    have hv : M.trajectoryExpectedValue π = fun _ ↦ M.trajectoryExpectedValue π s := by
      funext t
      rw [Subsingleton.elim t s]
    rw [hv, FiniteDistribution.expectation_const, FiniteDistribution.expectation_const]
    simp
  have hb := valueEstimator_perturbation M π N hN data 0 le_rfl hres
  simp only [mul_zero, zero_div] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-- A source-sized sample budget implies both the high-sample cutoff and
accuracy of the displayed radius, assuming the separately proved logarithmic
comparison `β ≤ 10 H`. -/
theorem source_sample_budget_arithmetic (h ε β H N : ℝ)
    (hh : 0 < h) (hε : 0 < ε) (hεh : ε ≤ 1 / h)
    (hβ : 0 ≤ β) (hβH : β ≤ 10 * H) (hN : 0 < N)
    (hNbound : 720 * H / (h ^ 3 * ε ^ 2) ≤ N) :
    64 * β / h ≤ N ∧ 3 * Real.sqrt (8 * β / (h ^ 3 * N)) ≤ ε := by
  have hden : 0 < h ^ 3 * ε ^ 2 := by positivity
  have hprod : 720 * H ≤ N * (h ^ 3 * ε ^ 2) := (div_le_iff₀ hden).mp hNbound
  have h72 : 72 * β ≤ N * (h ^ 3 * ε ^ 2) := by nlinarith
  have hhe : h * ε ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hh).mp hεh
  have hhe0 : 0 ≤ h * ε := by positivity
  have hhe2 : (h * ε) ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhe2 (mul_nonneg hN.le hh.le)
  have hbudget : N * (h ^ 3 * ε ^ 2) ≤ N * h := by nlinarith
  constructor
  · apply (div_le_iff₀ hh).2
    nlinarith
  · have harg : 8 * β / (h ^ 3 * N) ≤ (ε / 3) ^ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < h ^ 3 * N)).2
      nlinarith
    have hs : Real.sqrt (8 * β / (h ^ 3 * N)) ≤ ε / 3 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, harg⟩
    linarith

/-- For at least two states the event's inclusive-level logarithm is
controlled by the printed theorem's logarithm, at the source-selected depth. -/
theorem source_selected_depth_log_bound (h S δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hS : 2 ≤ S)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * Real.log (4 * S * ((⌈Real.log (Real.exp 1 / h)⌉₊ : ℝ) + 1) / δ) ≤
      10 * Real.log (S / (δ * h)) := by
  let x := Real.log (Real.exp 1 / h)
  let m := (⌈x⌉₊ : ℝ)
  let X := S / (δ * h)
  have hS0 : 0 < S := by linarith
  have hx : 0 ≤ x := by
    dsimp [x]
    rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hh), Real.log_exp]
    have hlog := Real.log_nonpos hh.le hh1
    linarith
  have hm := Nat.ceil_lt_add_one hx
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
  rw [Real.log_inv] at hlog
  have hinv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).2 hh1
  have hmupper : m + 1 ≤ 3 / h := by
    change (⌈Real.log (Real.exp 1 / h)⌉₊ : ℝ) + 1 ≤ 3 / h
    dsimp [x] at hm
    rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hh), Real.log_exp] at hm ⊢
    rw [div_eq_mul_inv]
    nlinarith
  have hδh : 0 < δ * h := mul_pos hδ hh
  have hX : 2 ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ hδh).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hh.le]
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < 4 * S * (m + 1) / δ := by
    have hm0 : 0 ≤ m := by dsimp [m]; positivity
    positivity
  have hYX : 4 * S * (m + 1) / δ ≤ 12 * X := by
    dsimp [X]
    have hhbound := mul_le_mul_of_nonneg_left hmupper (by positivity : 0 ≤ 4 * S / δ)
    convert hhbound using 1 <;> field_simp <;> norm_num
  have hX4 : (16 : ℝ) ≤ X ^ 4 := by
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hX 4
    norm_num at hp
    exact hp
  have hXX : 12 * X ≤ X ^ 5 := by
    have hp := mul_le_mul_of_nonneg_right hX4 hX0.le
    nlinarith [pow_succ X 4]
  have hlogle := Real.log_le_log hY0 (hYX.trans hXX)
  rw [Real.log_pow] at hlogle
  change 2 * Real.log (4 * S * (m + 1) / δ) ≤ 10 * Real.log X
  nlinarith

/-- With at least two states, the printed theorem's logarithm and the
explicit universal constant 720 imply both arithmetic requirements. -/
theorem source_sample_budget_from_printed_log (h S δ ε N : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hS : 2 ≤ S)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεh : ε ≤ 1 / h)
    (hN : 0 < N)
    (hNbound : 720 * Real.log (S / (δ * h)) / (h ^ 3 * ε ^ 2) ≤ N) :
    let β := 2 * Real.log (4 * S * ((⌈Real.log (Real.exp 1 / h)⌉₊ : ℝ) + 1) / δ)
    64 * β / h ≤ N ∧ 3 * Real.sqrt (8 * β / (h ^ 3 * N)) ≤ ε := by
  let m : ℝ := ⌈Real.log (Real.exp 1 / h)⌉₊
  let β := 2 * Real.log (4 * S * (m + 1) / δ)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hS0 : 0 < S := by linarith
  have harg : 1 ≤ 4 * S * (m + 1) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact mul_nonneg (by norm_num) (Real.log_nonneg harg)
  have hβH : β ≤ 10 * Real.log (S / (δ * h)) :=
    source_selected_depth_log_bound h S δ hh hh1 hS hδ hδ1.le
  exact source_sample_budget_arithmetic h ε β (Real.log (S / (δ * h))) N
    hh hε hεh hβ hβH hN hNbound

end StatisticalRL.ModelBasedPolicyEvaluation
