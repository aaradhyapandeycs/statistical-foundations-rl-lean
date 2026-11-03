import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Scalar arithmetic for the source main policy-learning sample theorem. -/
namespace StatisticalRL.ModelBasedPolicyLearning

/-- The source logarithms compare with factor ten when the finite count
product K is at least two. -/
theorem mainSample_log_comparison (h ε δ K : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hεmax : ε ≤ 1 / h) (hK : 2 ≤ K) :
    2 * Real.log (16 * K / (h * δ)) ≤
      10 * Real.log (K / (h ^ 2 * ε * δ)) := by
  have hhe : h * ε ≤ 1 := by nlinarith [(le_div_iff₀ hh).1 hεmax]
  let X := K / (h ^ 2 * ε * δ)
  let Y := 16 * K / (h * δ)
  have hden : 0 < h ^ 2 * ε * δ := by positivity
  have hden1 : h ^ 2 * ε * δ ≤ 1 := by
    have hm := mul_nonneg (sub_nonneg.mpr hhe) (show 0 ≤ h * δ by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hh1) hδ.le]
  have hX : (2 : ℝ) ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYX : Y ≤ 16 * X := by
    dsimp [Y, X]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < h * δ) hden).2
    have hm := mul_nonneg (sub_nonneg.mpr hhe) (show 0 ≤ 16 * K * h * δ by positivity)
    nlinarith
  have hlog := Real.log_le_log hY hYX
  have hlogX : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    calc
      _ = Real.log ((2 : ℝ) ^ (4 : ℕ)) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt (by linarith : 0 < X)), h16] at hlog
  change 2 * Real.log Y ≤ 10 * Real.log X
  linarith

/-- Once the source log comparison β≤10L is established, the printed budget
with constant 10240 supplies both the evaluation threshold and ε accuracy. -/
theorem mainSample_scalar_bounds (h ε β L n : ℝ)
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε ≤ 1 / h)
    (hβ : 0 ≤ β) (hβL : β ≤ 10 * L)
    (hbudget : 10240 * L / (h ^ 3 * ε ^ 2) ≤ n) :
    720 * β / h ≤ n ∧ 32 * Real.sqrt (β / (n * h ^ 3)) ≤ ε := by
  have hhe : h * ε ≤ 1 := by nlinarith [(le_div_iff₀ hh).1 hεmax]
  have hL : 0 ≤ L := by linarith
  have hn : 0 ≤ n := le_trans (by positivity) hbudget
  have hcore : 10240 * L ≤ n * (h ^ 3 * ε ^ 2) :=
    (div_le_iff₀ (by positivity)).1 hbudget
  have hsmall : h ^ 2 * ε ^ 2 ≤ 1 := by
    have hm := mul_self_le_mul_self (show 0 ≤ h * ε by positivity) hhe
    nlinarith
  have hthreshold : 720 * β ≤ n * h := by
    have hm := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hn hh.le)
    nlinarith
  constructor
  · exact (div_le_iff₀ hh).2 hthreshold
  · by_cases hn0 : n = 0
    · subst n
      simp [hε.le]
    · have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
      have hsq : β / (n * h ^ 3) ≤ (ε / 32) ^ 2 := by
        apply (div_le_iff₀ (by positivity : 0 < n * h ^ 3)).2
        nlinarith
      have hr : 0 ≤ Real.sqrt (β / (n * h ^ 3)) := Real.sqrt_nonneg _
      have hr2 := Real.sq_sqrt (show 0 ≤ β / (n * h ^ 3) by positivity)
      nlinarith [sq_nonneg (ε / 32)]

end StatisticalRL.ModelBasedPolicyLearning
