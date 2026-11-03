import Formalization.ModelFree.TDStepSizeBudget

/-!

Compatible numerical universal constants for the source TD variance and first-Freedman bounds.
-/
namespace StatisticalRL.TemporalDifference

/-- Concrete compatible constants for all numerical side conditions currently
used by the two assemblies, including the source ordering c2≤c1. -/
theorem tdSourceUniversalConstants_quarter_quarter_384 :
    (0 : ℝ) < 1/4 ∧ (1/4 : ℝ) ≤ 1/4 ∧
    (1/4 : ℝ)*(1/4) ≤ 1/8 ∧
    (384 : ℝ) > 0 ∧ (384 : ℝ) ≤ 384 ∧
    (4 : ℝ) ≤ (1/4)*384 ∧
    (1 : ℝ) ≤ (1/4)*384*Real.log 2^2 := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hsq : (1/4 : ℝ) ≤ Real.log 2^2 := by nlinarith
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  nlinarith

/-- The simultaneous side conditions are witnessed before any MDP, sample
budget, terminal, accuracy or confidence parameter is supplied. -/
theorem tdSourceUniversalConstants_exists :
    ∃ c₁ c₂ c₃ : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁*c₂ ≤ 1/8 ∧
      384 ≤ c₃ ∧ 4 ≤ c₁*c₃ ∧ 1 ≤ c₁*c₃*Real.log 2^2 := by
  rcases tdSourceUniversalConstants_quarter_quarter_384 with
    ⟨hpos, horder, hprod, _, hc₃, hlarge, hlog⟩
  exact ⟨1/4, 1/4, 384, hpos, hpos, horder, hprod, hc₃, hlarge, hlog⟩

end StatisticalRL.TemporalDifference
