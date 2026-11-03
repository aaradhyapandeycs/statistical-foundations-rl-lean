import Formalization.ModelFree.TDVarianceSum
import Formalization.Probability.FreedmanNaturalHistory

/-! Adapted fixed-terminal TD innovations and their exact natural-history tower.
Conditional variance under the smaller history retains an outer expectation. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdTerminalHistoryStateMeasurable : MeasurableSpace State := ⊤

/-- The current source coordinate enters the used prefix exactly at n+1. -/
theorem tdFreshCoordinate_measurable_nextPast (T n : ℕ) (hn : n < T) (s : State) :
    Measurable[tdPastSigma T (n + 1)] (fun data : TDSamples State T ↦ data (s,⟨n+1,by omega⟩)) := by
  let getFresh : ((i : tdPastIndices (State := State) T (n+1)) → State) → State :=
    fun code ↦ code ⟨(s,(⟨n+1,by omega⟩ : Fin (T+1))), by simp [tdPastIndices]⟩
  have hg : Measurable getFresh := measurable_of_countable _
  exact hg.comp (comap_measurable (tdPastData (State := State) T (n+1)))

theorem tdFreshIndicator_strong_nextPast (T n : ℕ) (hn : n < T) (s x : State) :
    StronglyMeasurable[tdPastSigma T (n+1)] (tdFreshIndicator T n hn s x) := by
  classical
  let f : State → ℝ := fun y ↦ if y = x then 1 else 0
  have hf : Measurable f := measurable_of_countable _
  exact (hf.comp (tdFreshCoordinate_measurable_nextPast T n hn s)).stronglyMeasurable

/-- Raw TD noise is measurable once its source update layer has been revealed. -/
theorem tdRowIncrement_strong_nextPast (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T n : ℕ) (hn : n < T) (V₀ : State → ℝ) (s : State) :
    StronglyMeasurable[tdPastSigma T (n+1)] (tdRowIncrement M π η T n hn V₀ s) := by
  classical
  have hm (x : State) : StronglyMeasurable[tdPastSigma T (n+1)]
      (fun data ↦ tdValueBefore M π η T n V₀ data x) :=
    (tdValueBefore_stronglyMeasurable M π η T n hn.le V₀ x).mono (tdPastSigma_mono T n (n+1) (by omega))
  have hmean := (tdRowMean_stronglyMeasurable M π η T n hn.le V₀ s).mono
    (tdPastSigma_mono T n (n+1) (by omega))
  have hfresh : StronglyMeasurable[tdPastSigma T (n+1)] (fun data : TDSamples State T ↦
      ∑ x, tdValueBefore M π η T n V₀ data x * tdFreshIndicator T n hn s x data) :=
    Finset.stronglyMeasurable_fun_sum _ fun x hx ↦ (hm x).mul (tdFreshIndicator_strong_nextPast T n hn s x)
  have he : tdRowIncrement M π η T n hn V₀ s = fun data : TDSamples State T ↦
      (∑ x, tdValueBefore M π η T n V₀ data x * tdFreshIndicator T n hn s x data) -
        tdRowMean M π s (tdValueBefore M π η T n V₀ data) := by
    funext data
    simp [tdRowIncrement, tdFreshIndicator]
  rw [he]
  exact hfresh.sub hmean

/-- Padding after the fixed terminal is proved for the actual source Z. -/
theorem tdTerminalIncrement_zero_after (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (s : State) (n : ℕ) (hn : t ≤ n) :
    tdTerminalIncrement M π η T t V₀ s n = 0 := by
  funext data
  simp only [tdTerminalIncrement, tdSampledWeightedIncrement, tdWeightedErrorIncrement,
    if_neg (by omega : ¬(1 ≤ n + 1 ∧ n + 1 ≤ t)), Pi.zero_apply]

/-- Genuine next-prefix adaptedness, including the padded infinite tail. -/
theorem tdTerminalIncrement_strong_nextPast (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) (n : ℕ) :
    StronglyMeasurable[tdSampleFiltration T (n+1)] (tdTerminalIncrement M π η T t V₀ s n) := by
  classical
  by_cases hn : n < t
  · have hnT : n < T := hn.trans_le ht
    rw [tdTerminalIncrement, tdSampledWeightedIncrement_eq_linearRow M π η T t n (by omega) ht V₀ s]
    unfold tdLinearRowIncrement
    exact Finset.stronglyMeasurable_fun_sum _ fun r hr ↦ stronglyMeasurable_const.mul
      (tdRowIncrement_strong_nextPast M π η T n hnT V₀ r)
  · rw [tdTerminalIncrement_zero_after M π η T t V₀ s n (by omega)]
    exact stronglyMeasurable_zero

/-- Increment-generated strict history is contained in the actual used prefix. -/
theorem tdTerminalPriorSigma_le_past (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) (n : ℕ) :
    priorIncrementSigma (tdTerminalIncrement M π η T t V₀ s) n ≤ tdPastSigma T n := by
  apply iSup₂_le
  intro j hj
  exact ((tdTerminalIncrement_strong_nextPast M π η T t ht V₀ s j).measurable.mono
    (tdPastSigma_mono T (j+1) n (by omega)) le_rfl).comap_le

/-- Centering on every actual sample prefix, with zero-padding after terminal. -/
theorem tdTerminalIncrement_condExp_past_zero (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) (n : ℕ) :
    (tdSamplingLaw M π T)[tdTerminalIncrement M π η T t V₀ s n | tdSampleFiltration T n]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  by_cases hn : n < t
  · exact tdSampledWeightedIncrement_condExp_zero M π η T t n (by omega) ht V₀ s
  · rw [tdTerminalIncrement_zero_after M π η T t V₀ s n (by omega), condExp_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The exact smaller-history centering follows from the tower property. -/
theorem tdTerminalIncrement_condExp_natural_zero (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) (n : ℕ) :
    (tdSamplingLaw M π T)[tdTerminalIncrement M π η T t V₀ s n |
      priorIncrementSigma (tdTerminalIncrement M π η T t V₀ s) n] =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  let m := priorIncrementSigma (tdTerminalIncrement M π η T t V₀ s) n
  have htower := condExp_condExp_of_le (μ := tdSamplingLaw M π T)
    (f := tdTerminalIncrement M π η T t V₀ s n)
    (tdTerminalPriorSigma_le_past M π η T t ht V₀ s n) (tdPastSigma_le T n)
  have hz := condExp_congr_ae (m := m) (tdTerminalIncrement_condExp_past_zero M π η T t ht V₀ s n)
  have hzero : (tdSamplingLaw M π T)[(0 : TDSamples State T → ℝ) | m] = 0 := condExp_zero
  exact htower.symm.trans (hz.trans (Filter.Eventually.of_forall fun data ↦ by
    change (tdSamplingLaw M π T)[(0 : TDSamples State T → ℝ) | m] data = 0
    rw [hzero]
    rfl))

/-- The smaller-history variance retains its OUTER conditional expectation;
the random raw-prefix variance is not silently treated as measurable there. -/
theorem tdTerminalIncrement_condExp_sq_natural (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t n : ℕ) (ht : t ≤ T) (hn : n < t) (V₀ : State → ℝ) (s : State) :
    (tdSamplingLaw M π T)[(fun data ↦ tdTerminalIncrement M π η T t V₀ s n data ^ 2) |
      priorIncrementSigma (tdTerminalIncrement M π η T t V₀ s) n] =ᵐ[tdSamplingLaw M π T]
    (tdSamplingLaw M π T)[(fun data ↦ ∑ r, tdWeightedPropagatorRow M π η t (n+1) s r ^ 2 *
      (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)) |
      priorIncrementSigma (tdTerminalIncrement M π η T t V₀ s) n] := by
  have h := condExp_condExp_of_le (μ := tdSamplingLaw M π T)
    (f := fun data ↦ tdTerminalIncrement M π η T t V₀ s n data ^ 2)
    (tdTerminalPriorSigma_le_past M π η T t ht V₀ s n) (tdPastSigma_le T n)
  have hv := condExp_congr_ae (m := priorIncrementSigma (tdTerminalIncrement M π η T t V₀ s) n)
    (tdSampledWeightedIncrement_condExp_sq M π η T t n (by omega) ht V₀ s)
  exact h.symm.trans hv

end StatisticalRL.TemporalDifference
