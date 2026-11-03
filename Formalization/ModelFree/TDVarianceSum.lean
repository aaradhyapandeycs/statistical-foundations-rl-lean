import Formalization.ModelFree.TDWeightedVariance
import Formalization.Probability.FreedmanExactAssembly

/-! Genuine used-sample filtration and fixed-terminal TD conditional-variance
summation. Adaptedness and deterministic late-time caps are separate targets. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdVarianceSumStateMeasurable : MeasurableSpace State := ⊤

noncomputable def tdRestrictPast (T m n : ℕ) (hmn : m ≤ n)
    (code : (i : tdPastIndices (State := State) T n) → State) :
    (i : tdPastIndices (State := State) T m) → State :=
  fun i ↦ code ⟨i.1, by
    apply Finset.mem_filter.mpr
    have hi := (Finset.mem_filter.mp i.2).2
    exact ⟨Finset.mem_univ _, hi.1, hi.2.trans hmn⟩⟩

theorem tdPastSigma_mono (T m n : ℕ) (hmn : m ≤ n) :
    tdPastSigma (State := State) T m ≤ tdPastSigma T n := by
  have hr : Measurable (tdRestrictPast (State := State) T m n hmn) := measurable_of_countable _
  have hp : Measurable[tdPastSigma T n] (tdPastData (State := State) T n) := comap_measurable _
  have he : tdRestrictPast T m n hmn ∘ tdPastData T n = tdPastData (State := State) T m := by
    funext data i
    rfl
  have hcomp := hr.comp hp
  rw [he] at hcomp
  exact hcomp.comap_le

/-- The actual used-prefix sigma-algebras form a genuine filtration. Time zero
is excluded from each prefix by definition, not silently observed. -/
noncomputable def tdSampleFiltration (T : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (TDSamples State T)) where
  seq := tdPastSigma T
  mono' := fun m n hmn ↦ tdPastSigma_mono T m n hmn
  le' := fun n ↦ tdPastSigma_le T n

/-- Infinite-indexed sequence at FIXED terminal t: source Z_(n+1)^t.
The actual Z definition pads indices after the terminal with zero. -/
noncomputable def tdTerminalIncrement (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (s : State) (n : ℕ) : TDSamples State T → ℝ :=
  tdSampledWeightedIncrement M π η T t (n + 1) V₀ s

noncomputable def tdTerminalVarianceSum (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (s : State) : TDSamples State T → ℝ :=
  predictableSecondMomentSum (tdSamplingLaw M π T) (tdSampleFiltration T)
    (tdTerminalIncrement M π η T t V₀ s) t

noncomputable def tdTerminalVarianceProxy (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (s : State) (data : TDSamples State T) : ℝ :=
  ∑ n ∈ Finset.range t, M.discount ^ 2 * tdRateWeight M.discount η t (n + 1) * η (n + 1) *
    tdErrorPropagate M π η (n + 1) t
      (fun r ↦ (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)) s

/-- The full exact squared-row variance identity is summed on one a.e. event,
with the fixed terminal retained in every coefficient. -/
theorem tdTerminalVarianceSum_eq_squaredRows (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) :
    tdTerminalVarianceSum M π η T t V₀ s =ᵐ[tdSamplingLaw M π T] fun data ↦
      ∑ n ∈ Finset.range t, ∑ r, tdWeightedPropagatorRow M π η t (n + 1) s r ^ 2 *
        (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data) := by
  have hp (n : Fin t) := tdSampledWeightedIncrement_condExp_sq M π η T t n.val (by omega) ht V₀ s
  filter_upwards [ae_all_iff.mpr hp] with data hd
  unfold tdTerminalVarianceSum predictableSecondMomentSum
  simp only [tdSampleFiltration, tdTerminalIncrement]
  apply Finset.sum_congr rfl
  intro n hn
  exact hd ⟨n, Finset.mem_range.mp hn⟩

/-- Source per-step proxies sum to the actual used-filtration variance proxy.
No desired deterministic cap or late-time estimate is a premise. -/
theorem tdTerminalVarianceSum_le_proxy (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤ tdTerminalVarianceProxy M π η T t V₀ s data := by
  have hp (n : Fin t) := tdSampledWeightedIncrement_variance_proxy M π η T t n.val (by omega) ht V₀ s hη
  filter_upwards [ae_all_iff.mpr hp] with data hd
  unfold tdTerminalVarianceSum predictableSecondMomentSum tdTerminalVarianceProxy
  simp only [tdSampleFiltration, tdTerminalIncrement]
  apply Finset.sum_le_sum
  intro n hn
  exact hd ⟨n, Finset.mem_range.mp hn⟩

end StatisticalRL.TemporalDifference
