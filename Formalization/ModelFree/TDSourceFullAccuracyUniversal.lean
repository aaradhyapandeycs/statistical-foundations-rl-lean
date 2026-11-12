import Formalization.ModelFree.TDSourceFinalAccuracyComposition
import Formalization.ModelFree.TDSourceFirstFreedmanAssembly
import Formalization.ModelFree.TDSourceVarianceProxyLemma
import Formalization.ModelFree.TDInitialErrorContraction

/-! Source-facing terminal-accuracy wrapper. It derives terminal eligibility,
instantiates the actual-law first-Freedman and variance results, converts the
variance result to the coordinatewise interface, and supplies the deterministic
initial-error bound. All helper events and numerical side conditions are derived
internally from the model, finite source schedule and sample budget. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

local instance tdSourceFullAccuracyStateMeasurable (State : Type*) :
    MeasurableSpace State := ⊤

/-- Source-facing terminal-accuracy theorem with universal constants. -/
theorem tdSource_policyEvaluation_accuracy_exists_universal_constants :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ)^3 *
        Real.log ((Fintype.card State : ℝ)*T/δ) /
          ((1-M.discount)^3*ε^2) ≤ T →
      1-δ ≤ (tdSamplingLaw M π T).real
        {data | ∀ s : State,
          |tdErrorValue M π η (tdSamplesExtend M T data) V₀ T s| ≤ ε} := by
  let c₃ : ℝ := max 4096 (Real.exp 4 / Real.log 2 ^ 4)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 2 ^ 4 := pow_pos hlog2 4
  have hc₃low : 4096 ≤ c₃ := le_max_left _ _
  have hc₃pos : 0 < c₃ := by dsimp [c₃]; positivity
  have hterminal : Real.exp 4 ≤ c₃ * Real.log 2 ^ 4 := by
    have hratio : Real.exp 4 / Real.log 2 ^ 4 ≤ c₃ := le_max_right _ _
    exact (div_le_iff₀ hlog4).mp hratio
  have hterminalQuarter : Real.exp (1 / (1/4 : ℝ)) ≤
      c₃ * Real.log 2 ^ 4 := by
    convert hterminal using 1 <;> norm_num
  refine ⟨1/4, 1/4, c₃, by norm_num, by norm_num, by norm_num,
    hc₃pos, ?_⟩
  intro State Action instState instAction M π η δ ε T hγ hT
    hδ hδ1 hε hεmax hsource V₀ h₀ hbudget
  letI : Nonempty State := M.state_nonempty
  have hS : 1 ≤ Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hSreal : 1 ≤ (Fintype.card State : ℝ) := by exact_mod_cast hS
  have htime := tdSource_final_terminal_eligible_of_budget M (1/4) c₃ ε δ T
    hT (by norm_num) hc₃pos hterminalQuarter hδ hδ1 hε hεmax hbudget
  have hstep : TDStepSizeSchedule M.discount (1/4) (1/4) T η := by
    simpa only [TDStepSizeSchedule, tdSourceRateSchedule] using hsource
  have hc₁c₃ : (4 : ℝ) ≤ (1/4) * c₃ := by
    have hmul := mul_le_mul_of_nonneg_left hc₃low
      (by norm_num : (0 : ℝ) ≤ 1/4)
    linarith [hmul]
  have hprod : (1/4 : ℝ) * (1/4) ≤ 1/8 := by norm_num
  have hc₃large : (384 : ℝ) ≤ c₃ := le_trans (by norm_num) hc₃low
  have hc₃final : (3168 : ℝ) ≤ c₃ := le_trans (by norm_num) hc₃low
  have hconstVariance : 1 ≤ (1/4) * c₃ * Real.log 2 ^ 2 := by
    have hloghalf : (1/2 : ℝ) ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    have hsq : (1/4 : ℝ) ≤ Real.log 2 ^ 2 :=
      calc (1/4 : ℝ) = (1/2) ^ 2 := by norm_num
        _ ≤ Real.log 2 ^ 2 := pow_le_pow_left₀ (by norm_num) hloghalf 2
    have hmul := mul_le_mul hc₁c₃ hsq (by norm_num) (by positivity)
    linarith [hmul]
  have hfirst := tdSource_firstFreedman_allStates_of_budget M π η T T hT
    (1/4) (1/4) c₃ ε δ (by norm_num) (by norm_num) hc₁c₃ hprod
    hc₃large hγ hδ hδ1 hε hεmax hbudget hstep V₀ h₀ (le_rfl : T ≤ T) htime
  have hvarianceNorm := tdSource_varianceProxy_both_of_budget M π η T T hT
    (1/4) (1/4) c₃ ε δ (by norm_num) (by norm_num) hc₃large hprod
    hconstVariance hγ hδ hδ1 hε hεmax hbudget hsource V₀ h₀
    (le_rfl : T ≤ T) htime
  have hvariance : 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ‖tdSourceFixedTerminalProxyVector M π η T T V₀
            (tdSourceBarEta M.discount T) data‖ ≤
              16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
          ∀ s : State,
            tdTerminalVarianceSum M π η T T V₀ s data ≤
              33 * Real.log (T : ℝ) ^ 3 /
                ((1 - M.discount) ^ 3 * T)} := by
    let sourceEvent : Set (TDSamples State T) := {data |
      ‖tdSourceFixedTerminalProxyVector M π η T T V₀
          (tdSourceBarEta M.discount T) data‖ ≤
            16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
      ‖fun s => tdTerminalVarianceSum M π η T T V₀ s data‖ ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)}
    let targetEvent : Set (TDSamples State T) := {data |
      ‖tdSourceFixedTerminalProxyVector M π η T T V₀
          (tdSourceBarEta M.discount T) data‖ ≤
            16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
      ∀ s : State, tdTerminalVarianceSum M π η T T V₀ s data ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)}
    have hsubset : sourceEvent ⊆ targetEvent := by
      intro data hd
      refine ⟨hd.1, ?_⟩
      intro s
      have habs : |tdTerminalVarianceSum M π η T T V₀ s data| ≤
          33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T) := by
        have hn := (norm_le_pi_norm
          (fun q => tdTerminalVarianceSum M π η T T V₀ q data) s).trans hd.2
        simpa only [Real.norm_eq_abs] using hn
      exact (le_abs_self _).trans habs
    have hmono := ENNReal.toReal_mono
      (measure_ne_top (tdSamplingLaw M π T) targetEvent)
      (measure_mono hsubset)
    change 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real sourceEvent at hvarianceNorm
    change 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real targetEvent
    exact hvarianceNorm.trans hmono
  have hinitial := tdInitialError_contraction_of_source_budget M π η T T
    (1/4) (1/4) c₃ ε δ hT (by norm_num) (by norm_num) hc₃pos
    hconstVariance hδ hδ1 hε hεmax hstep hprod hbudget (le_rfl : T ≤ T)
    htime V₀ h₀
  have hfinal := tdSource_final_accuracy_of_events M π η T T c₃ ε δ
    (Fintype.card State : ℝ) V₀ hT (le_rfl : T ≤ T) hγ
    M.discount_lt_one hSreal rfl hδ hδ1 hε hεmax hc₃final hbudget
    hfirst hvariance hinitial
  exact hfinal

end StatisticalRL.TemporalDifference
