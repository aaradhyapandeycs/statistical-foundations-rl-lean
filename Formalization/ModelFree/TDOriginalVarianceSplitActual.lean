import Formalization.ModelFree.TDEarlyVarianceBudget
import Formalization.ModelFree.TDSharpVarianceSum
import Formalization.ModelFree.TDSourceRateFiniteExtension
import Formalization.ModelFree.TDSourceRateProxyTransport
import Formalization.ModelFree.TDSourceFreedmanBudgetSmallness

/-!

Actual original TD predictable variance split into early squared rows and the late proxy.
-/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdOriginalSplitActualStateMeasurable : MeasurableSpace State := ⊤

/-- The late source squared-row contribution is below the matching actual
random-proxy term, by actual nonnegative row mass and the late scalar weight. -/
theorem tdOriginalSquaredRow_late_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t n : ℕ) (hn : n < t) (V₀ : State → ℝ)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hw : tdRateWeight M.discount η t (n+1) ≤ barη)
    (s : State) (data : TDSamples State T) :
    (∑ r, tdWeightedPropagatorRow M π η t (n+1) s r ^ 2 *
      (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)) ≤
      barη * η (n+1) * M.discount^2 *
        ∑ r, tdSquareLateTerminalRow M π η t (n+1) s r *
          (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data) := by
  let v := fun r => (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)
  have hv : ∀ r, 0 ≤ v r := fun r => (M.policyTransition π r).variance_nonneg _
  have hA : 0 ≤ ∑ r, tdPropagatorRow M π η (n+1) t s r * v r :=
    Finset.sum_nonneg (fun r _ => mul_nonneg
      (tdPropagatorRow_nonneg M π η (n+1) t hη s r) (hv r))
  have hηk : 0 ≤ η (n+1) := (hη (n+1) (by omega) (by omega)).1
  have hh := td_nonnegative_row_variance_proxy
    (tdWeightedPropagatorRow M π η t (n+1) s) v
    (tdWeightedPropagatorRow_nonneg M π η t (n+1) (by omega) (by omega) hη s) hv
  rw [tdWeightedPropagatorRow_sum M π η t (n+1) (by omega) (by omega) s,
    tdWeightedPropagatorRow_apply, tdErrorPropagate_eq_row_sum] at hh
  have hm := mul_le_mul_of_nonneg_right hw
    (mul_nonneg (mul_nonneg (sq_nonneg M.discount) hηk) hA)
  dsimp [v, tdSquareLateTerminalRow] at *
  nlinarith [hh, hm]

/-- The actual original predictable variance has an a.e. early-squared-row
plus late-proxy bound, with all three objects on the same law and same data. -/
theorem tdOriginalVarianceSum_le_earlyRows_add_lateProxy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ)
    (hlate : ∀ k, t/2+1 ≤ k → k ≤ t → tdRateWeight M.discount η t k ≤ barη)
    (s : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤
        tdEarlySquaredVarianceRows M π η T t V₀ s data +
          tdSquareLateWindowRandomProxy M π η T t V₀ barη s data := by
  filter_upwards [tdTerminalVarianceSum_eq_squaredRows M π η T t ht V₀ s] with data heq
  rw [heq]
  unfold tdEarlySquaredVarianceRows tdSquareLateWindowRandomProxy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnt : n < t := Finset.mem_range.mp hn
  by_cases he : n < t/2
  · simp only [if_pos he, if_neg (by omega : ¬t/2 ≤ n), add_zero]
    exact le_rfl
  · simp only [if_neg he, if_pos (by omega : t/2 ≤ n), zero_add]
    exact tdOriginalSquaredRow_late_le M π η T t n hnt V₀ hη barη
      (hlate (n+1) (by omega) (by omega)) s data

/-- Source finite schedule and corrected early-weight large-T premise give
the original-W split, without a target variance estimate as an input. -/
theorem tdOriginalVarianceSum_source_early_late
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T t : ℕ) (hT : 2 ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcprod : c₁*c₂ ≤ 1/8)
    (hlarge : Real.log (T : ℝ)^2 ≤ c₁*(1-M.discount)*T)
    (hs : TDStepSizeSchedule M.discount c₁ c₂ T η)
    (ht : t ≤ T) (helig : tdSourceEligibleTerminal T c₂ t)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (s : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤
        M.discount^2 * M.effectiveHorizon^2/(2*(T : ℝ)^3) +
          tdSquareLateWindowRandomProxy M π η T t V₀
            (tdSourceBarEta M.discount T) s data := by
  have hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi hit
    exact td_schedule_rate_bounds M.discount c₁ c₂ T η hT M.discount_lt_one
      hc₁ hc₂ hs i hi (hit.trans ht)
  have hsource : tdSourceRateSchedule M.discount c₁ c₂ T η := by
    simpa only [TDStepSizeSchedule, tdSourceRateSchedule] using hs
  have hlate : ∀ k, t/2+1 ≤ k → k ≤ t →
      tdRateWeight M.discount η t k ≤ tdSourceBarEta M.discount T := by
    intro k hkl hkt
    have hrate := tdSourceRateSchedule_eligible_late_le M.discount c₁ c₂ T t k
      hT ht M.discount_lt_one hc₂ η hsource helig hkl hkt
    exact (tdRateWeight_le_rate M.discount η t k M.discount_nonneg
      M.discount_lt_one.le (by omega) hkt hη).trans hrate
  have hearly := tdEarlySquaredVarianceRows_le_budget_of_source_schedule M π η
    c₁ c₂ T t hT hc₁ hc₂ hcprod hlarge hs ht helig V₀ h₀ s
  filter_upwards [tdOriginalVarianceSum_le_earlyRows_add_lateProxy M π η T t ht
    V₀ hη (tdSourceBarEta M.discount T) hlate s] with data hd
  exact hd.trans (add_le_add (hearly data) le_rfl)

end StatisticalRL.TemporalDifference
