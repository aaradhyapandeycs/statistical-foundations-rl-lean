import Formalization.ModelFree.TDOriginalVarianceCommonEvent

/-!

Both source TD variance-proxy inequalities on one actual-law fixed-terminal event.
-/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSourceVarianceLemmaStateMeasurable : MeasurableSpace State := ⊤

/-- Both printed variance-proxy bounds, simultaneously at one source-eligible
terminal under the actual synchronous TD sampling law. All numerical
conditions below constrain the source universal constants, not the outcome. -/
theorem tdSource_varianceProxy_both_of_budget
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (hT : 2 ≤ T)
    (c₁ c₂ c₃ ε δ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 384 ≤ c₃)
    (hcprod : c₁*c₂ ≤ 1/8)
    (hconstants : 1 ≤ c₁*c₃*Real.log 2^2)
    (hγhalf : 1/2 ≤ M.discount)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεmax : ε ≤ M.effectiveHorizon)
    (hBudget : c₃ * Real.log (T : ℝ)^3 *
        Real.log ((Fintype.card State : ℝ)*T/δ) /
          ((1-M.discount)^3*ε^2) ≤ T)
    (hSched : tdSourceRateSchedule M.discount c₁ c₂ T η)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (ht : t ≤ T) (helig : tdSourceEligibleTerminal T c₂ t) :
    1-δ/(2*T) ≤ (tdSamplingLaw M π T).real
      {data |
        ‖tdSourceFixedTerminalProxyVector M π η T t V₀
          (tdSourceBarEta M.discount T) data‖ ≤
            16*tdSourceBarEta M.discount T*M.effectiveHorizon^2 ∧
        ‖fun s => tdTerminalVarianceSum M π η T t V₀ s data‖ ≤
          33*Real.log (T : ℝ)^3/((1-M.discount)^3*T)} := by
  have hs : TDStepSizeSchedule M.discount c₁ c₂ T η := by
    simpa only [TDStepSizeSchedule, tdSourceRateSchedule] using hSched
  have hsplit := tdOriginalVarianceSum_source_early_late_of_budget M π η
    c₁ c₂ c₃ ε δ T t hT hc₁ hc₂ (by linarith) hcprod hconstants
    hδ hδ1 hε hεmax hBudget hs ht helig V₀ h₀
  have hprob := tdSource_fixedTerminalProxy_of_budget M π η T t hT
    c₁ c₂ c₃ ε δ hc₁ hc₂ hc₃ hγhalf hδ hδ1 hε hεmax hBudget
    hSched V₀ h₀ ht helig
  have hscale := tdOriginalVarianceScale_combine M.discount M.effectiveHorizon
    (tdSourceBarEta M.discount T) T hγhalf M.discount_lt_one hT
    rfl rfl
  have hD : 0 ≤ 33*Real.log (T : ℝ)^3/((1-M.discount)^3*T) := by
    have hlog : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ T))
    have hgap : 0 ≤ 1-M.discount := sub_nonneg.mpr M.discount_lt_one.le
    positivity
  exact tdOriginalVariance_commonEvent_of_split M π η T t ht V₀
    (tdSourceBarEta M.discount T)
    (M.discount^2*M.effectiveHorizon^2/(2*(T : ℝ)^3))
    (16*tdSourceBarEta M.discount T*M.effectiveHorizon^2)
    (33*Real.log (T : ℝ)^3/((1-M.discount)^3*T))
    (1-δ/(2*T)) hD hscale hsplit hprob

end StatisticalRL.TemporalDifference
