import Formalization.ModelFree.TDSourceFixedTerminalProxyBudget
import Formalization.ModelFree.TDVarianceSum

/-! Compose the actual fixed-terminal proxy event with an actual-law early/late
variance split. The split is supplied per state almost everywhere and assembled
into a common full-measure event using finiteness of the state space. The scalar
33-scale comparison remains an explicit premise. -/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdVarianceLemmaCompositionStateMeasurable : MeasurableSpace State := ⊤

/-- Compose the actual fixed-terminal proxy event with an actual-law early/late
split. The split is supplied per state as an a.e. statement; finiteness of the
state set assembles one common full-measure split event. The scalar comparison
is separately supplied. Consequently the two source conclusions hold
simultaneously with the proxy event's exact probability lower bound. -/
theorem tdVarianceLemmaComposition_of_proxy_split_scale
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (barη δ : ℝ)
    (hProxy : 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤
          16 * barη * M.effectiveHorizon ^ 2})
    (hSplit : ∀ s : State, ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤
        M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) +
          tdSquareLateWindowRandomProxy M π η T t V₀ barη s data)
    (hScale : M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) +
        16 * barη * M.effectiveHorizon ^ 2 ≤
          33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)) :
    1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤
            16 * barη * M.effectiveHorizon ^ 2 ∧
          ∀ s : State,
            tdTerminalVarianceSum M π η T t V₀ s data ≤
              33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)} := by
  classical
  let μ : Measure (TDSamples State T) := tdSamplingLaw M π T
  let proxyGood : Set (TDSamples State T) :=
    {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤
      16 * barη * M.effectiveHorizon ^ 2}
  let target : Set (TDSamples State T) :=
    {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤
        16 * barη * M.effectiveHorizon ^ 2 ∧
      ∀ s : State,
        tdTerminalVarianceSum M π η T t V₀ s data ≤
          33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)}
  have hSplitAll : ∀ᵐ data ∂μ, ∀ s : State,
      tdTerminalVarianceSum M π η T t V₀ s data ≤
        M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) +
          tdSquareLateWindowRandomProxy M π η T t V₀ barη s data := by
    apply ae_all_iff.mpr
    intro s
    exact hSplit s
  have hgoodSubset : proxyGood ≤ᵐ[μ] target := by
    filter_upwards [hSplitAll] with data hsplit hproxy
    refine ⟨hproxy, ?_⟩
    intro s
    have hcoordNorm := (norm_le_pi_norm
      (tdSourceFixedTerminalProxyVector M π η T t V₀ barη data) s).trans hproxy
    have hcoordAbs :
        |tdSquareLateWindowRandomProxy M π η T t V₀ barη s data| ≤
          16 * barη * M.effectiveHorizon ^ 2 := by
      simpa [tdSourceFixedTerminalProxyVector, Real.norm_eq_abs] using hcoordNorm
    have hcoord :
        tdSquareLateWindowRandomProxy M π η T t V₀ barη s data ≤
          16 * barη * M.effectiveHorizon ^ 2 :=
      (le_abs_self _).trans hcoordAbs
    calc
      tdTerminalVarianceSum M π η T t V₀ s data ≤
          M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) +
            tdSquareLateWindowRandomProxy M π η T t V₀ barη s data := hsplit s
      _ ≤ M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) +
            16 * barη * M.effectiveHorizon ^ 2 := by nlinarith [hcoord]
      _ ≤ 33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T) := hScale
  have hmeasure : μ proxyGood ≤ μ target := measure_mono_ae hgoodSubset
  have hreal : μ.real proxyGood ≤ μ.real target :=
    ENNReal.toReal_mono (measure_ne_top μ target) hmeasure
  change 1 - δ / (2 * (T : ℝ)) ≤ μ.real target
  change 1 - δ / (2 * (T : ℝ)) ≤ μ.real proxyGood at hProxy
  exact hProxy.trans hreal

end StatisticalRL.TemporalDifference
