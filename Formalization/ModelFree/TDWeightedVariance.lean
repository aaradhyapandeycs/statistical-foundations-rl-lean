import Formalization.ModelFree.TDPropagatorRows

/-! Actual fixed-terminal source TD innovation conditional moments and proxy.
No late-time uniform cap, target variance estimate or martingale premise is used. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdWeightedVarianceStateMeasurable : MeasurableSpace State := ⊤

/-- The actual source Z_j^t evaluated on the same finite TD sample experiment. -/
noncomputable def tdSampledWeightedIncrement (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t j : ℕ)
    (V₀ : State → ℝ) (s : State) (data : TDSamples State T) : ℝ :=
  tdWeightedErrorIncrement M π η (tdSamplesExtend M T data) V₀ t j s

/-- Exact row identification uses the ACTUAL chronological row and raw noise,
with source update j=k+1 and fixed final t≤T. -/
theorem tdSampledWeightedIncrement_eq_linearRow (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t k : ℕ)
    (hkt : k + 1 ≤ t) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) :
    tdSampledWeightedIncrement M π η T t (k + 1) V₀ s =
      tdLinearRowIncrement M π η T k (by omega) V₀ (tdWeightedPropagatorRow M π η t (k + 1) s) := by
  funext data
  rw [tdSampledWeightedIncrement, tdWeightedErrorIncrement_eq_row_sum M π η
    (tdSamplesExtend M T data) V₀ t (k + 1) (by omega) hkt s]
  unfold tdLinearRowIncrement
  apply Finset.sum_congr rfl
  intro r hr
  have he := congrFun (tdRowIncrement_eq_centeredRowNoise M π η T k (by omega) V₀ r) data
  exact congrArg (fun x : ℝ ↦ tdWeightedPropagatorRow M π η t (k + 1) s r * x) he.symm

/-- Deterministic linear combinations inherit conditional centering from the
actual raw-row theorem, rather than taking a martingale fact as a premise. -/
theorem tdLinearRowIncrement_condExp_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T k : ℕ) (hk : k < T)
    (V₀ : State → ℝ) (u : State → ℝ) :
    (tdSamplingLaw M π T)[tdLinearRowIncrement M π η T k hk V₀ u | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  classical
  let ξ r := tdRowIncrement M π η T k hk V₀ r
  have he : tdLinearRowIncrement M π η T k hk V₀ u = ∑ r, (u r) • ξ r := by
    funext data
    simp only [tdLinearRowIncrement, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ξ]
  rw [he]
  have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
    (f := fun r ↦ (u r) • ξ r) (fun r hr ↦ tdSampling_integrable M π T _) (tdPastSigma T k)
  have hterm (r : State) : (tdSamplingLaw M π T)[(u r) • ξ r | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
    have hs := condExp_smul (μ := tdSamplingLaw M π T) (u r) (ξ r) (tdPastSigma T k)
    filter_upwards [hs, tdRowIncrement_condExp_zero M π η T k hk V₀ r] with data hd hz
    simpa only [ξ, Pi.smul_apply, smul_eq_mul, hz, mul_zero] using hd
  filter_upwards [hsum, ae_all_iff.mpr hterm] with data hd hterms
  rw [hd]
  simp only [Finset.sum_apply]
  simp only [hterms, Finset.sum_const_zero]

/-- The fixed-terminal actual source innovation is conditionally centered. -/
theorem tdSampledWeightedIncrement_condExp_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t k : ℕ)
    (hkt : k + 1 ≤ t) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) :
    (tdSamplingLaw M π T)[tdSampledWeightedIncrement M π η T t (k + 1) V₀ s | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  rw [tdSampledWeightedIncrement_eq_linearRow M π η T t k hkt ht V₀ s]
  exact tdLinearRowIncrement_condExp_zero M π η T k (by omega) V₀ _

/-- Exact conditional variance/second moment of the actual propagated source
innovation, retaining the squared ACTUAL weighted row coefficients. -/
theorem tdSampledWeightedIncrement_condExp_sq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t k : ℕ)
    (hkt : k + 1 ≤ t) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) :
    (tdSamplingLaw M π T)[(fun data ↦ tdSampledWeightedIncrement M π η T t (k + 1) V₀ s data ^ 2) | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun data ↦ ∑ r,
        tdWeightedPropagatorRow M π η t (k + 1) s r ^ 2 *
          (M.policyTransition π r).variance (tdValueBefore M π η T k V₀ data) := by
  rw [tdSampledWeightedIncrement_eq_linearRow M π η T t k hkt ht V₀ s]
  exact tdLinearRowIncrement_condExp_sq M π η T k (by omega) V₀ _

/-- Source eq:TD-var-Zk-upper-bound-each-term, derived for the actual fixed
terminal source innovation. No target variance estimate is a premise. -/
theorem tdSampledWeightedIncrement_variance_proxy (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t k : ℕ)
    (hkt : k + 1 ≤ t) (ht : t ≤ T) (V₀ : State → ℝ) (s : State)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      (tdSamplingLaw M π T)[(fun data ↦ tdSampledWeightedIncrement M π η T t (k + 1) V₀ s data ^ 2) | tdPastSigma T k] data ≤
        M.discount ^ 2 * tdRateWeight M.discount η t (k + 1) * η (k + 1) *
          tdErrorPropagate M π η (k + 1) t
            (fun r ↦ (M.policyTransition π r).variance (tdValueBefore M π η T k V₀ data)) s := by
  have hu := tdWeightedPropagatorRow_nonneg M π η t (k + 1) (by omega) hkt hη s
  have hp := tdLinearRowIncrement_condExp_sq_le M π η T k (by omega) V₀
    (tdWeightedPropagatorRow M π η t (k + 1) s) hu
  rw [← tdSampledWeightedIncrement_eq_linearRow M π η T t k hkt ht V₀ s] at hp
  filter_upwards [hp] with data hd
  rw [tdWeightedPropagatorRow_sum M π η t (k + 1) (by omega) hkt s,
    tdWeightedPropagatorRow_apply] at hd
  calc
    _ ≤ (M.discount * tdRateWeight M.discount η t (k + 1)) *
        (M.discount * η (k + 1) * tdErrorPropagate M π η (k + 1) t
          (fun r ↦ (M.policyTransition π r).variance (tdValueBefore M π η T k V₀ data)) s) := hd
    _ = _ := by ring

end StatisticalRL.TemporalDifference
