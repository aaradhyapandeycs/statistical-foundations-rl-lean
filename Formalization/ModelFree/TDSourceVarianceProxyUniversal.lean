import Formalization.ModelFree.TDSourceVarianceProxyLemma
import Formalization.ModelFree.TDSourceUniversalConstants

/-!

Source TD variance-proxy inequalities with universal constants chosen before all problem parameters.
-/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
universe u v
local instance tdSourceVarianceUniversalMeasurable (State : Type*) :
    MeasurableSpace State := ⊤

/-- A compatible larger c3 also meets the separately drafted final scalar
absorption requirement. This only checks numerical conditions, not final TD
accuracy or any unconsumed proof obligation. -/
theorem tdSourceUniversalConstants_quarter_quarter_4096 :
    (0 : ℝ) < 1/4 ∧ (1/4 : ℝ) ≤ 1/4 ∧
    (1/4 : ℝ)*(1/4) ≤ 1/8 ∧
    (3168 : ℝ) ≤ 4096 ∧ (384 : ℝ) ≤ 4096 ∧
    (4 : ℝ) ≤ (1/4)*4096 ∧
    (1 : ℝ) ≤ (1/4)*4096*Real.log 2^2 := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hsq : (1/4 : ℝ) ≤ Real.log 2^2 := by nlinarith
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩
  nlinarith

/-- Source Lemma 4.5: choose compatible universal constants before the finite
carriers, model, policy, rates, confidence, accuracy and terminal. Both printed
infinity-norm inequalities hold on the same actual-law event. -/
theorem tdSource_varianceProxy_exists_universal_constants :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 < c₃ ∧
    ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T t : ℕ),
      1/2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ)^3 *
        Real.log ((Fintype.card State : ℝ)*T/δ) /
          ((1-M.discount)^3*ε^2) ≤ T →
      t ≤ T → tdSourceEligibleTerminal T c₂ t →
      1-δ/(2*T) ≤ (tdSamplingLaw M π T).real
        {data |
          ‖tdSourceFixedTerminalProxyVector M π η T t V₀
            (tdSourceBarEta M.discount T) data‖ ≤
              16*tdSourceBarEta M.discount T*M.effectiveHorizon^2 ∧
          ‖fun s => tdTerminalVarianceSum M π η T t V₀ s data‖ ≤
            33*Real.log (T : ℝ)^3/((1-M.discount)^3*T)} := by
  rcases tdSourceUniversalConstants_quarter_quarter_4096 with
    ⟨hpos, horder, hprod, _, hlarge, _, hlog⟩
  refine ⟨1/4, 1/4, 4096, hpos, horder, by norm_num, by norm_num, ?_⟩
  intro State Action instState instAction M π η δ ε T t hγ hT
    hδ hδ1 hε hεmax hs V₀ h₀ hbudget ht helig
  exact tdSource_varianceProxy_both_of_budget M π η T t hT
    (1/4) (1/4) 4096 ε δ hpos hpos hlarge hprod hlog
    hγ hδ hδ1 hε hεmax hbudget hs V₀ h₀ ht helig

end StatisticalRL.TemporalDifference
