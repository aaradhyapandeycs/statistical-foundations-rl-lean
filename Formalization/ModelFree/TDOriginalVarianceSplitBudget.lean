import Formalization.ModelFree.TDOriginalVarianceSplitActual
import Formalization.ModelFree.TDStepSizeBudget

/-!

The source sample budget supplies the actual TD early/late variance split.
-/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdOriginalSplitBudgetStateMeasurable : MeasurableSpace State := ⊤

/-- Actual original-W early/late split from the source main budget, with the
universal-constant relations explicit rather than an extra large-T premise. -/
theorem tdOriginalVarianceSum_source_early_late_of_budget
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (c₁ c₂ c₃ ε δ : ℝ) (T t : ℕ) (hT : 2 ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hcprod : c₁*c₂ ≤ 1/8)
    (hconstants : 1 ≤ c₁*c₃*Real.log 2^2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεmax : ε ≤ M.effectiveHorizon)
    (hbudget : c₃ * Real.log (T : ℝ)^3 *
        Real.log ((Fintype.card State : ℝ)*T/δ) /
          ((1-M.discount)^3 * ε^2) ≤ T)
    (hs : TDStepSizeSchedule M.discount c₁ c₂ T η)
    (ht : t ≤ T) (helig : tdSourceEligibleTerminal T c₂ t)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (s : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤
        M.discount^2 * M.effectiveHorizon^2/(2*(T : ℝ)^3) +
          tdSquareLateWindowRandomProxy M π η T t V₀
            (tdSourceBarEta M.discount T) s data := by
  letI : Nonempty State := M.state_nonempty
  have hS : 1 ≤ Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hlarge := td_mainBudget_implies_large c₁ c₃ M.discount δ ε
    (Fintype.card State) T hc₁ hc₃ hconstants hS hT M.discount_lt_one
    hδ hδ1 hε hεmax hbudget
  exact tdOriginalVarianceSum_source_early_late M π η c₁ c₂ T t hT
    hc₁ hc₂ hcprod hlarge hs ht helig V₀ h₀ s

end StatisticalRL.TemporalDifference
