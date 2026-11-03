import Formalization.ModelFree.TDOriginalVarianceSplitBudget
import Formalization.ModelFree.TDOriginalVarianceScale
import Formalization.ModelFree.TDSourceFixedTerminalProxyBudget

/-!

Add the actual original-variance norm bound to the same TD late-proxy event.
-/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdOriginalCommonEventStateMeasurable : MeasurableSpace State := ⊤

/-- The actual first predictable variance is nonnegative a.e., directly from
its proved actual squared-row identity; no positivity conclusion is assumed. -/
theorem tdOriginalVarianceSum_nonneg_ae
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      0 ≤ tdTerminalVarianceSum M π η T t V₀ s data := by
  filter_upwards [tdTerminalVarianceSum_eq_squaredRows M π η T t ht V₀ s] with data heq
  rw [heq]
  exact Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun r _ =>
    mul_nonneg (sq_nonneg _) ((M.policyTransition π r).variance_nonneg _)))

/-- An a.e. actual split upgrades the existing proxy event to both infinity-
norm bounds on the same event, without another confidence allocation.
The split input is a proved intermediate supplied by the preceding module. -/
theorem tdOriginalVariance_commonEvent_of_split
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (barη E C D p : ℝ) (hD : 0 ≤ D) (hscale : E+C ≤ D)
    (hsplit : ∀ s, ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤ E +
        tdSquareLateWindowRandomProxy M π η T t V₀ barη s data)
    (hprob : p ≤ (tdSamplingLaw M π T).real
      {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤ C}) :
    p ≤ (tdSamplingLaw M π T).real
      {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤ C ∧
        ‖fun s => tdTerminalVarianceSum M π η T t V₀ s data‖ ≤ D} := by
  have hsplitAll : ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      tdTerminalVarianceSum M π η T t V₀ s data ≤ E +
        tdSquareLateWindowRandomProxy M π η T t V₀ barη s data :=
    ae_all_iff.mpr hsplit
  have hnonnegAll : ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      0 ≤ tdTerminalVarianceSum M π η T t V₀ s data :=
    ae_all_iff.mpr (fun s => tdOriginalVarianceSum_nonneg_ae M π η T t ht V₀ s)
  have hsubset : ∀ᵐ data ∂tdSamplingLaw M π T,
      data ∈ {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤ C} →
      data ∈ {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤ C ∧
        ‖fun s => tdTerminalVarianceSum M π η T t V₀ s data‖ ≤ D} := by
    filter_upwards [hsplitAll, hnonnegAll] with data hsplitData hn hgood
    refine ⟨hgood, (pi_norm_le_iff_of_nonneg hD).2 (fun s => ?_)⟩
    have hp := (norm_le_pi_norm
      (tdSourceFixedTerminalProxyVector M π η T t V₀ barη data) s).trans hgood
    have hpupper : tdSquareLateWindowRandomProxy M π η T t V₀ barη s data ≤ C :=
      (le_abs_self _).trans (by
        simpa [tdSourceFixedTerminalProxyVector, Real.norm_eq_abs] using hp)
    have hu := (hsplitData s).trans ((add_le_add (le_refl E) hpupper).trans hscale)
    simpa only [Real.norm_eq_abs] using
      (abs_le.mpr ⟨(neg_nonpos.mpr hD).trans (hn s), hu⟩)
  exact hprob.trans (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae hsubset))

end StatisticalRL.TemporalDifference
