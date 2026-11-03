import Formalization.ModelFree.TDTerminalCaps

/-! Scalar fixed-terminal Freedman event for the actual
synchronous TD sequence. It consumes proved cap helpers, not assumed caps.
The deterministic weight envelope remains an explicit bounded-helper input. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdFreedmanStateMeasurable : MeasurableSpace State := ⊤

/-- Source update indexing agrees exactly with the genuine finite-history sum. -/
theorem tdTerminalIncrement_sum_eq_source (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (s : State) (data : TDSamples State T) :
    incrementSum (tdTerminalIncrement M π η T t V₀ s) t data =
      ∑ k ∈ Finset.Icc 1 t, tdSampledWeightedIncrement M π η T t k V₀ s data := by
  change (∑ n ∈ Finset.range t, tdSampledWeightedIncrement M π η T t (n+1) V₀ s data) = _
  exact td_sum_range_succ_eq_Icc (fun k ↦ tdSampledWeightedIncrement M π η T t k V₀ s data) t

/-- Actual scalar TD confidence event at a fixed terminal and coordinate.
There is no martingale, independence, increment-cap or variance-cap premise:
all are discharged through the actual prefix and cap helpers. The bound is
conservative and does not assert the source main TD accuracy theorem. -/
theorem tdTerminal_freedman_weightEnvelope (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (s : State) (A : ℝ) (hA : 0 ≤ A)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hcap : ∀ k, 1 ≤ k → k ≤ t → tdRateWeight M.discount η t k ≤ A)
    (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (tdSamplingLaw M π T).real {data |
      |∑ k ∈ Finset.Icc 1 t, tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
      Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
        ((M.discount ^ 2 * M.effectiveHorizon ^ 3 * A) / (2 : ℝ) ^ K) *
          Real.log (2 * K / δ)) +
        (4 / 3) * (2 * M.discount * M.effectiveHorizon * A) * Real.log (2 * K / δ)} := by
  have hB : 0 ≤ 2 * M.discount * M.effectiveHorizon * A := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) M.discount_nonneg)
      M.effectiveHorizon_nonneg) hA
  have hσ : 0 ≤ M.discount ^ 2 * M.effectiveHorizon ^ 3 * A := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg M.effectiveHorizon_nonneg 3)) hA
  have hb (n : ℕ) : ∀ᵐ data ∂tdSamplingLaw M π T,
      |tdTerminalIncrement M π η T t V₀ s n data| ≤ 2 * M.discount * M.effectiveHorizon * A :=
    Filter.Eventually.of_forall fun data ↦
      tdTerminalIncrement_abs_le_weight_cap M π η T t V₀ h₀ s A hA hη hcap n data
  have hp := freedman_source_bound (tdSamplingLaw M π T) (tdSampleFiltration T)
    (tdTerminalIncrement M π η T t V₀ s)
    (2 * M.discount * M.effectiveHorizon * A) (M.discount ^ 2 * M.effectiveHorizon ^ 3 * A)
    hB hσ (tdTerminalIncrement_strong_nextPast M π η T t ht V₀ s) hb
    (tdTerminalIncrement_condExp_past_zero M π η T t ht V₀ s) t K hK
    (tdTerminalVarianceSum_le_weight_cap M π η T t ht V₀ h₀ s A hA hη hcap) δ hδ hδ1
  simpa only [tdTerminalIncrement_sum_eq_source, tdTerminalVarianceSum] using hp

end StatisticalRL.TemporalDifference
