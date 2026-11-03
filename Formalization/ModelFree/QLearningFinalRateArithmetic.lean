import Formalization.ModelFree.QLearningChiSourceParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! deterministic source final-rate arithmetic.
No estimate of actual Q error or comparator closeness is assumed here. -/
namespace StatisticalRL.QLearning

/-- Source log(4R)<=3log R with its exact domain R>=2. -/
theorem qFinal_log_four_mul_le (R : ℝ) (hR : 2 ≤ R) :
    Real.log (4 * R) ≤ 3 * Real.log R := by
  have hRp : 0 < R := by linarith
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hR
  have hfour : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (ne_of_gt hRp), hfour]
  linarith

/-- Source scalar rho consequences, preserving the full epsilon<=1/h domain.
Here d denotes c2*c3*log T after the separately derived budget conversion. -/
theorem qFinal_rho_terms (γ h ε ρ d : ℝ)
    (_hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hh : 0 < h) (hhhalf : h ≤ 1/2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/h) (hρ : 0 ≤ ρ) (hd : 384 ≤ d)
    (hbudget : ρ ≤ 48 * ε^2 * h^3 / d) :
    ρ ≤ 1/16 ∧ Real.sqrt (γ*ρ/(2*h^3)) ≤ ε/4 ∧ 2*ρ/h^2 ≤ ε/4 := by
  have hdp : 0 < d := by linarith
  have heh : ε*h ≤ 1 := (le_div_iff₀ hh).mp hεmax
  have hesq : ε^2*h^2 ≤ 1 := by
    have hs := (sq_le_sq₀ (mul_nonneg hε.le hh.le) (by norm_num : (0:ℝ)≤1)).2 heh
    simpa only [mul_pow, one_pow] using hs
  have hesq3 : ε^2*h^3 ≤ h := by nlinarith [mul_le_mul_of_nonneg_right hesq hh.le]
  have hb := (le_div_iff₀ hdp).mp hbudget
  have h384 := mul_le_mul_of_nonneg_left hd hρ
  have hrho : ρ ≤ 1/16 := by nlinarith
  have h8 : 8*ρ ≤ ε^2*h^3 := by nlinarith
  have hγρ : γ*ρ ≤ ρ := mul_le_of_le_one_left hρ hγ1
  have hsqrt : Real.sqrt (γ*ρ/(2*h^3)) ≤ ε/4 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < 2*h^3)).2
    nlinarith
  have heps3 : ε^2*h^3 ≤ ε*h^2 := by
    have hm := mul_le_mul_of_nonneg_right heh (by positivity : 0 ≤ ε*h^2)
    nlinarith
  have hlin : 2*ρ/h^2 ≤ ε/4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hh)).2
    nlinarith
  exact ⟨hrho, hsqrt, hlin⟩

/-- Source comparison coefficient simplification on the proved small-rho range. -/
theorem qFinal_comparison_coefficient_le (ρ : ℝ) (_hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1/16) :
    1 + 2*ρ + Real.sqrt ρ ≤ 2 := by
  have hs : Real.sqrt ρ ≤ 1/4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  linarith

/-- A sufficient transient comparison using an elementary budget consequence.
The final source budget must prove epsilon*h*T>=1 rather than assume it. -/
theorem qFinal_transient_le_half (h ε T : ℝ) (hh : 0 < h) (_hε : 0 < ε)
    (hT : 2 ≤ T) (hbudget : 1 ≤ ε*h*T) : 2/(h*T^4) ≤ ε/2 := by
  have hTp : 0 < T := by linarith
  apply (div_le_iff₀ (by positivity : 0 < h*T^4)).2
  have hcube : 8 ≤ T^3 := by nlinarith [sq_nonneg (T-2), sq_nonneg (T+2)]
  have hm := mul_le_mul_of_nonneg_right hbudget (by positivity : 0 ≤ T^3)
  nlinarith

/-- Source final scalar expression is at most epsilon once its separately
proved rho and product-decay consequences have been supplied. It is an
arithmetic helper, not an assumed or concluded actual Q-error estimate. -/
theorem qFinal_scalar_radius_le (γ h ε ρ d P T : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hh : 0 < h) (hhhalf : h ≤ 1/2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/h) (hρ : 0 ≤ ρ) (hd : 384 ≤ d)
    (hrhobudget : ρ ≤ 48*ε^2*h^3/d)
    (hT : 2 ≤ T) (htransient : 1 ≤ ε*h*T) (hP : P ≤ 1/T^4) :
    ((1+2*ρ+Real.sqrt ρ)/h)*P + Real.sqrt (γ*ρ/(2*h^3)) + 2*ρ/h^2 ≤ ε := by
  obtain ⟨hrho, hsqrt, hlin⟩ := qFinal_rho_terms γ h ε ρ d hγ hγ1 hh hhhalf hε hεmax hρ hd hrhobudget
  have hcoeff := qFinal_comparison_coefficient_le ρ hρ hrho
  have hfirst : ((1+2*ρ+Real.sqrt ρ)/h)*P ≤ 2/(h*T^4) := by
    calc
      _ ≤ ((1+2*ρ+Real.sqrt ρ)/h)*(1/T^4) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      _ ≤ (2/h)*(1/T^4) := mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hh).2 hcoeff) (by positivity)
      _ = _ := by ring
  have ht := qFinal_transient_le_half h ε T hh hε hT htransient
  linarith

/-- Pointwise sandwich plus separately established comparator closeness yields
an actual pointwise error bound; desired error is not a premise. -/
theorem qFinal_sandwich_error {q low high target C D : ℝ}
    (hs : low-C ≤ q ∧ q ≤ high+C)
    (hlow : |low-target| ≤ D) (hhigh : |high-target| ≤ D) : |q-target| ≤ C+D := by
  have hl := abs_le.mp hlow
  have hh := abs_le.mp hhigh
  exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩

end StatisticalRL.QLearning
