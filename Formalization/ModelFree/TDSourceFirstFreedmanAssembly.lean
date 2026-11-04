import Formalization.ModelFree.TDSourceFirstFreedmanComparisons

/-! Assemble the actual-law all-state first-Freedman event with the finite
source schedule and printed sample budget. The large-time inequality is derived
from the budget under the explicit source-constant relation `4 ≤ c₁*c₃`; that
relation remains visible because the other numerical hypotheses do not imply
it. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The sample budget forces the rate-schedule large-time side condition,
provided the chosen universal constants obey `4 ≤ c₁*c₃`. -/
theorem tdSourceBudget_implies_schedule_large
    (γ c₁ c₃ ε δ S : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (hc₃ : 0 < c₃) (hc₁c₃ : 4 ≤ c₁ * c₃)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hS : 1 ≤ S)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - γ))
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (S * T / δ) / ((1 - γ) ^ 3 * ε ^ 2) ≤ (T : ℝ)) :
    Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T := by
  have hgap : 0 < 1 - γ := by linarith
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 1 / 2 ≤ Real.log (T : ℝ) := by
    have hlog2 : Real.log 2 ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have hlog2half : 1 / 2 ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      linarith
    exact hlog2half.trans hlog2
  have hlogT0 : 0 ≤ Real.log (T : ℝ) := by linarith
  have hST : 2 ≤ S * T := by
    have hTtwo : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : 0 ≤ (T : ℝ))]
  have hq : 2 < S * T / δ := by
    rw [lt_div_iff₀ hδ]
    nlinarith [hST, hδ1]
  have hqpos : 0 < S * T / δ := by positivity
  have hlogq : 1 / 2 ≤ Real.log (S * T / δ) := by
    have hlogineq := Real.one_sub_inv_le_log_of_pos hqpos
    have hinv : (S * T / δ)⁻¹ < 1 / 2 := by
      rw [inv_lt_iff_one_lt_mul₀' hqpos]
      nlinarith [hq]
    linarith
  have hlogq0 : 0 ≤ Real.log (S * T / δ) := by linarith
  have hden : 0 < (1 - γ) ^ 3 * ε ^ 2 :=
    mul_pos (pow_pos hgap 3) (sq_pos_of_pos hε)
  have hbudgetNumerator :
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) ≤
        (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) :=
    (div_le_iff₀ hden).mp hBudget
  have hgeps : (1 - γ) * ε ≤ 1 := by
    calc
      (1 - γ) * ε ≤ (1 - γ) * (1 / (1 - γ)) :=
        mul_le_mul_of_nonneg_left hεmax hgap.le
      _ = 1 := by field_simp
  have hgepsNonneg : 0 ≤ (1 - γ) * ε := mul_nonneg hgap.le hε.le
  have hgepsSq : ((1 - γ) * ε) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hgepsNonneg (sub_nonneg.mpr hgeps)]
  have hdenReduce : (1 - γ) ^ 3 * ε ^ 2 ≤ 1 - γ := by
    calc
      (1 - γ) ^ 3 * ε ^ 2 = (1 - γ) * ((1 - γ) * ε) ^ 2 := by ring
      _ ≤ (1 - γ) * 1 := mul_le_mul_of_nonneg_left hgepsSq hgap.le
      _ = 1 - γ := by ring
  have hbudgetReduce :
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) ≤
        (T : ℝ) * (1 - γ) := by
    exact hbudgetNumerator.trans
      (mul_le_mul_of_nonneg_left hdenReduce hTpos.le)
  have hfourth :
      (c₃ / 4) * Real.log (T : ℝ) ^ 2 ≤
        c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) := by
    have hprod : (1 / 4 : ℝ) ≤
        Real.log (T : ℝ) * Real.log (S * T / δ) := by
      nlinarith [mul_le_mul hlogT hlogq (by norm_num : (0 : ℝ) ≤ 1 / 2) hlogT0]
    have hmul := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg hc₃.le (sq_nonneg (Real.log (T : ℝ))))
    nlinarith [hmul]
  have hscale : Real.log (T : ℝ) ^ 2 ≤
      (4 / c₃) * ((T : ℝ) * (1 - γ)) := by
    have hscaleNum : c₃ * Real.log (T : ℝ) ^ 2 ≤
        4 * ((T : ℝ) * (1 - γ)) := by
      nlinarith [hfourth, hbudgetReduce]
    have hscaleNum' : Real.log (T : ℝ) ^ 2 * c₃ ≤
        4 * ((T : ℝ) * (1 - γ)) := by nlinarith [hscaleNum]
    calc
      Real.log (T : ℝ) ^ 2 ≤
          (4 * ((T : ℝ) * (1 - γ))) / c₃ := (le_div_iff₀ hc₃).2 hscaleNum'
      _ = (4 / c₃) * ((T : ℝ) * (1 - γ)) := by ring
  have hcoeff : 4 / c₃ ≤ c₁ := by
    rw [div_le_iff₀ hc₃]
    exact hc₁c₃
  have htarget := mul_le_mul_of_nonneg_right hcoeff
    (mul_nonneg hTpos.le hgap.le)
  have htarget' : (4 / c₃) * ((T : ℝ) * (1 - γ)) ≤
      c₁ * (1 - γ) * T := by
    calc
      (4 / c₃) * ((T : ℝ) * (1 - γ)) ≤
          c₁ * ((T : ℝ) * (1 - γ)) := htarget
      _ = c₁ * (1 - γ) * T := by ring
  exact hscale.trans htarget'

/-- Budget-fed source all-state first-Freedman event. The actual finite source
schedule, its source terminal range, and sample budget produce every cap and
logarithm input to the union helper. Only the universal-constant relation
`4≤c₁*c₃` is explicit in addition to the printed sufficient-constant bounds;
the schedule large-time premise is proved internally above. -/
theorem tdSource_firstFreedman_allStates_of_budget
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (hT : 2 ≤ T)
    (c₁ c₂ c₃ ε δ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁c₃ : 4 ≤ c₁ * c₃)
    (hcprod : c₁ * c₂ ≤ 1 / 8) (hc₃ : 384 ≤ c₃)
    (hγhalf : 1 / 2 ≤ M.discount)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεmax : ε ≤ M.effectiveHorizon)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ))
    (hSched : TDStepSizeSchedule M.discount c₁ c₂ T η)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (ht : t ≤ T)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t) :
    1 - δ / (2 * (T : ℝ)) ≤ (tdSamplingLaw M π T).real
      {data | ∀ s : State,
        |∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
          Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
            ((3 * Real.log (T : ℝ) ^ 3 /
              ((1 - M.discount) ^ 4 * T)) /
              (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) *
              (3 * Real.log ((Fintype.card State : ℝ) * T / δ))) +
          (4 / 3) * (4 * M.discount * Real.log (T : ℝ) ^ 3 /
            ((1 - M.discount) ^ 2 * T)) *
            (3 * Real.log ((Fintype.card State : ℝ) * T / δ))} := by
  have hγ1 : M.discount < 1 := M.discount_lt_one
  have hS : 1 ≤ (Fintype.card State : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr M.state_nonempty
  have hlarge := tdSourceBudget_implies_schedule_large
    M.discount c₁ c₃ ε δ (Fintype.card State : ℝ) T hT hγhalf hγ1
    (by linarith) hc₁c₃ hδ hδ1 hS hε hεmax hBudget
  have hcomparisons := tdSource_firstFreedman_comparisons M η T t c₁ c₂ c₃
    ε δ hc₁ hc₂ hcprod hc₃ hT hγhalf hδ hδ1 hε hεmax hBudget hlarge
    hSched ht htime
  rcases hcomparisons with ⟨hK, hA, hcap, hη, hB, hSigma, hLog⟩
  simpa [tdSourceBarEta, tdSourceFreedmanLevel, mul_assoc, mul_left_comm,
    mul_comm] using
    (tdSource_firstFreedman_allStates_of_caps M π η T t ht V₀ h₀
      (tdSourceBarEta M.discount T)
      (4 * M.discount * Real.log (T : ℝ) ^ 3 /
        ((1 - M.discount) ^ 2 * T))
      (3 * Real.log (T : ℝ) ^ 3 /
        ((1 - M.discount) ^ 4 * T))
      (3 * Real.log ((Fintype.card State : ℝ) * T / δ)) δ
      hA hη hcap hB hSigma (tdSourceFreedmanLevel M.discount) hK
      δ hδ hδ1 hLog)

end StatisticalRL.TemporalDifference
