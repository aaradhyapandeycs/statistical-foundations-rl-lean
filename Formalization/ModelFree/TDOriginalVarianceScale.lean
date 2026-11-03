import Formalization.ModelFree.TDSourceFreedmanBudgetSmallness

/-!

Scalar comparison of the TD early and late variance contributions with the source 33 scale.
-/
namespace StatisticalRL.TemporalDifference

/-- The two contributions produced by the source variance split and proxy
bound fit within the stated `33 log³(T)/((1−γ)³ T)` scale. The source theorem
ensures `T≥2`, the explicit horizon assumption of the source main theorem. The weaker
`T≥2` bound suffices for the scalar comparison. -/
theorem tdOriginalVarianceScale_combine
    (γ H barη : ℝ) (T : ℕ)
    (hγhalf : 1 / 2 ≤ γ) (hγone : γ < 1) (hT2 : 2 ≤ T)
    (hH : H = 1 / (1 - γ))
    (hbarη : barη = tdSourceBarEta γ T) :
    γ ^ 2 * H ^ 2 / (2 * (T : ℝ) ^ 3) + 16 * barη * H ^ 2 ≤
      33 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 3 * T) := by
  have hgap : 0 < 1 - γ := by linarith
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hTreal2 : 2 ≤ (T : ℝ) := by exact_mod_cast hT2
  have hlog2half : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogT : 1 / 2 ≤ Real.log (T : ℝ) := by
    have hlogmono : Real.log 2 ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast (by omega : 2 ≤ T))
    exact hlog2half.trans hlogmono
  have hlogTnonneg : 0 ≤ Real.log (T : ℝ) := by linarith
  have hlogTcube : 1 / 8 ≤ Real.log (T : ℝ) ^ 3 := by
    have hsquare : 1 / 4 ≤ Real.log (T : ℝ) ^ 2 := by nlinarith [hlogT]
    have hmul := mul_le_mul_of_nonneg_left hsquare hlogTnonneg
    nlinarith [hmul]
  have hTsq : 4 ≤ (T : ℝ) ^ 2 := by nlinarith
  have hbig : 1 ≤ 2 * (T : ℝ) ^ 2 * Real.log (T : ℝ) ^ 3 := by
    have hmul := mul_le_mul hTsq hlogTcube
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (sq_nonneg (T : ℝ))
    nlinarith [hmul]
  have hγnonneg : 0 ≤ γ := by linarith
  have hγsq : γ ^ 2 ≤ 1 := by
    have hh : 0 ≤ (1-γ)*(1+γ) := mul_nonneg
      (sub_nonneg.mpr hγone.le) (by linarith)
    nlinarith [hh]
  have hgap_le_one : 1 - γ ≤ 1 := by linarith
  have hgap_nonneg : 0 ≤ 1 - γ := hgap.le
  have hgammaGap : γ ^ 2 * (1 - γ) ≤ 1 := by
    calc
      γ ^ 2 * (1 - γ) ≤ 1 * (1 - γ) :=
        mul_le_mul_of_nonneg_right hγsq hgap_nonneg
      _ ≤ 1 := by nlinarith
  have hmain : γ ^ 2 * (1 - γ) ≤
      2 * (T : ℝ) ^ 2 * Real.log (T : ℝ) ^ 3 := hgammaGap.trans hbig
  have hfirst : γ ^ 2 / (2 * (1 - γ) ^ 2 * (T : ℝ) ^ 3) ≤
      Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 3 * T) := by
    rw [div_le_div_iff₀
      (by positivity : 0 < 2 * (1 - γ) ^ 2 * (T : ℝ) ^ 3)
      (by positivity : 0 < (1 - γ) ^ 3 * T)]
    calc
      γ ^ 2 * ((1 - γ) ^ 3 * T) =
          (γ ^ 2 * (1 - γ)) * ((1 - γ) ^ 2 * T) := by ring
      _ ≤ (2 * (T : ℝ) ^ 2 * Real.log (T : ℝ) ^ 3) *
          ((1 - γ) ^ 2 * T) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
      _ = Real.log (T : ℝ) ^ 3 *
          (2 * (1 - γ) ^ 2 * (T : ℝ) ^ 3) := by ring
  rw [hH, hbarη, tdSourceBarEta]
  calc
    _ ≤ Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 3 * T) +
        16 * (2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)) *
          (1 / (1 - γ)) ^ 2 := by
      have heq : γ^2 * (1/(1-γ))^2 / (2*(T : ℝ)^3) =
          γ^2 / (2*(1-γ)^2*(T : ℝ)^3) := by
        field_simp [ne_of_gt hgap, ne_of_gt hTpos]
      rw [heq]
      exact add_le_add hfirst le_rfl
    _ = 33 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 3 * T) := by
      field_simp [ne_of_gt hgap, ne_of_gt hTpos]
      ring

end StatisticalRL.TemporalDifference
