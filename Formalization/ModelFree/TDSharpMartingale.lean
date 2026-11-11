import Formalization.ModelFree.TDSharpEnergy
import Formalization.ModelFree.TDTerminalHistory
import Formalization.Probability.FreedmanNaturalHistory
import Mathlib.Probability.ConditionalExpectation

/-! Centered-square martingale increments for a
fixed terminal TD variance-energy argument. The future propagator coefficients
are deterministic functions of the source rates and the fixed terminal; this
module asserts no Freedman bound or variance cap. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpMartingaleStateMeasurable : MeasurableSpace State := ⊤

/-- Actual squared iterate at source update k, under the finite synchronous
sampling law. -/
noncomputable def tdSquareObservation (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s : State) : TDSamples State T → ℝ :=
  fun data ↦ tdValueBefore M π η T k V₀ data s ^ 2

/-- Conditional mean of the actual squared iterate, given used source samples
through time k−1. This is the conditional expectation in Lemma 4.4. -/
noncomputable def tdSquareConditionalMean (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s : State) : TDSamples State T → ℝ :=
  (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s | tdPastSigma T (k - 1)]

/-- Centering is with respect to the actual preceding sample prefix, not a
nominal row expectation or a larger history. -/
noncomputable def tdSquareCentered (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s : State) : TDSamples State T → ℝ :=
  tdSquareObservation M π η T V₀ k s - tdSquareConditionalMean M π η T V₀ k s

theorem tdSquareCentered_condExp_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s : State) :
    (tdSamplingLaw M π T)[tdSquareCentered M π η T V₀ k s | tdPastSigma T (k - 1)]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  let f := tdSquareObservation M π η T V₀ k s
  let m := tdPastSigma (State := State) T (k - 1)
  let g := (tdSamplingLaw M π T)[f | m]
  have hsub := condExp_sub (tdSampling_integrable M π T f)
    (tdSampling_integrable M π T g) m
  have hfix : (tdSamplingLaw M π T)[g | m] = g := by
    change (tdSamplingLaw M π T)[(tdSamplingLaw M π T)[f | m] | m] =
      (tdSamplingLaw M π T)[f | m]
    exact condExp_of_stronglyMeasurable (tdPastSigma_le T (k - 1))
      stronglyMeasurable_condExp (tdSampling_integrable M π T g)
  change (tdSamplingLaw M π T)[f - g | m] =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0
  filter_upwards [hsub] with data hs
  rw [hs, hfix]
  simp [g]

theorem tdSquareCentered_strong_nextPast (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (hk : k ≤ T) (s : State) :
    StronglyMeasurable[tdPastSigma T k] (tdSquareCentered M π η T V₀ k s) := by
  have hobs : StronglyMeasurable[tdPastSigma T k]
      (tdSquareObservation M π η T V₀ k s) :=
    (tdValueBefore_stronglyMeasurable M π η T k hk V₀ s).pow 2
  have hmean : StronglyMeasurable[tdPastSigma T k]
      (tdSquareConditionalMean M π η T V₀ k s) := by
    exact stronglyMeasurable_condExp.mono
      (tdPastSigma_mono T (k - 1) k (by omega))
  exact hobs.sub hmean

/-- Fixed-terminal centered-square innovation after applying the actual
chronological tail. On the source late window this is Z-tilde at k=n+1; this helper also includes earlier updates. -/
noncomputable def tdSquareTerminalIncrement (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (s : State) (n : ℕ) : TDSamples State T → ℝ :=
  if n < t then fun data ↦
    tdErrorPropagate M π η (n + 1) t
      (fun r ↦ tdSquareCentered M π η T V₀ (n + 1) r data) s
  else fun _ ↦ 0

theorem tdSquareTerminalIncrement_strong_nextPast
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (s : State) (n : ℕ) :
    StronglyMeasurable[tdSampleFiltration T (n + 1)]
      (tdSquareTerminalIncrement M π η T t V₀ s n) := by
  classical
  by_cases hn : n < t
  · rw [tdSquareTerminalIncrement, if_pos hn]
    have hrow (data : TDSamples State T) :
        tdErrorPropagate M π η (n + 1) t
            (fun r ↦ tdSquareCentered M π η T V₀ (n + 1) r data) s =
          ∑ r, tdPropagatorRow M π η (n + 1) t s r *
            tdSquareCentered M π η T V₀ (n + 1) r data :=
      tdErrorPropagate_eq_row_sum M π η (n + 1) t _ s
    have hfun : (fun data : TDSamples State T ↦
        tdErrorPropagate M π η (n + 1) t
          (fun r ↦ tdSquareCentered M π η T V₀ (n + 1) r data) s) =
        ∑ r, fun data ↦ tdPropagatorRow M π η (n + 1) t s r *
          tdSquareCentered M π η T V₀ (n + 1) r data := by
      funext data
      simp only [Finset.sum_apply]
      exact hrow data
    rw [hfun]
    have hsum : StronglyMeasurable[tdSampleFiltration T (n + 1)]
        (fun data ↦ ∑ r : State, tdPropagatorRow M π η (n + 1) t s r *
          tdSquareCentered M π η T V₀ (n + 1) r data) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro r hr
      exact stronglyMeasurable_const.mul
        (tdSquareCentered_strong_nextPast M π η T V₀ (n + 1) (by omega) r)
    have hsumEq : (∑ r : State, fun data : TDSamples State T ↦
        tdPropagatorRow M π η (n + 1) t s r *
          tdSquareCentered M π η T V₀ (n + 1) r data) =
        (fun data ↦ ∑ r : State, tdPropagatorRow M π η (n + 1) t s r *
          tdSquareCentered M π η T V₀ (n + 1) r data) := by
      funext data
      simp only [Finset.sum_apply]
    rw [hsumEq]
    exact hsum
  · rw [tdSquareTerminalIncrement, if_neg hn]
    exact stronglyMeasurable_const

theorem tdSquareTerminalIncrement_condExp_past_zero
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (s : State) (n : ℕ) :
    (tdSamplingLaw M π T)[tdSquareTerminalIncrement M π η T t V₀ s n |
      tdSampleFiltration T n] =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  classical
  by_cases hn : n < t
  · have hk : 1 ≤ n + 1 := by omega
    have hkT : n + 1 ≤ T := by omega
    rw [tdSquareTerminalIncrement, if_pos hn]
    let m := tdPastSigma (State := State) T n
    let f (r : State) : TDSamples State T → ℝ := fun data ↦
      tdPropagatorRow M π η (n + 1) t s r *
        tdSquareCentered M π η T V₀ (n + 1) r data
    have hrep : (fun data : TDSamples State T ↦
        tdErrorPropagate M π η (n + 1) t
          (fun r ↦ tdSquareCentered M π η T V₀ (n + 1) r data) s) = ∑ r, f r := by
      funext data
      simp only [Finset.sum_apply]
      exact tdErrorPropagate_eq_row_sum M π η (n + 1) t _ s
    rw [hrep]
    have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
      (f := f) (fun r hr ↦ tdSampling_integrable M π T (f r)) m
    have hterm (r : State) :
        (tdSamplingLaw M π T)[f r | m] =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
      have hpull := condExp_mul_of_stronglyMeasurable_left
        (stronglyMeasurable_const : StronglyMeasurable[m]
          (fun _ : TDSamples State T ↦ tdPropagatorRow M π η (n + 1) t s r))
        (tdSampling_integrable M π T (f r))
        (tdSampling_integrable M π T (tdSquareCentered M π η T V₀ (n + 1) r))
      change (tdSamplingLaw M π T)[(fun _ : TDSamples State T ↦
        tdPropagatorRow M π η (n + 1) t s r) *
          tdSquareCentered M π η T V₀ (n + 1) r | m] =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0
      have hcenter := tdSquareCentered_condExp_zero M π η T V₀ (n + 1) r
      have hcenter' : (tdSamplingLaw M π T)[tdSquareCentered M π η T V₀ (n + 1) r | m]
          =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
        simpa [m] using hcenter
      filter_upwards [hpull, hcenter'] with data hp hz
      rw [hp]
      change tdPropagatorRow M π η (n + 1) t s r *
        ((tdSamplingLaw M π T)[tdSquareCentered M π η T V₀ (n + 1) r | m] data) = 0
      rw [hz]
      simp
    filter_upwards [hsum, ae_all_iff.mpr hterm] with data hs hterms
    change (tdSamplingLaw M π T)[∑ r, f r | tdPastSigma T n] data = 0
    rw [hs]
    simp only [Finset.sum_apply]
    simp [hterms]
  · rw [tdSquareTerminalIncrement, if_neg hn]
    change (tdSamplingLaw M π T)[(0 : TDSamples State T → ℝ) | tdSampleFiltration T n]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0
    rw [condExp_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

theorem tdSquareTerminalIncrement_priorSigma_le_past
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (s : State) (n : ℕ) :
    priorIncrementSigma (tdSquareTerminalIncrement M π η T t V₀ s) n ≤
      tdPastSigma T n := by
  apply iSup₂_le
  intro j hj
  exact ((tdSquareTerminalIncrement_strong_nextPast M π η T t ht V₀ s j).measurable.mono
    (tdPastSigma_mono T (j + 1) n (by omega)) le_rfl).comap_le

end StatisticalRL.TemporalDifference
