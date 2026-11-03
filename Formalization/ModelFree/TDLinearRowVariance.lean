import Formalization.ModelFree.TDCrossCovariance

/-! Conditional variance of deterministic linear combinations of actual TD
row noises. The actual propagated source row is to be identified separately. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdLinearVarianceStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance tdLinearVarianceStateDecidable : DecidableEq State := Classical.decEq State

/-- A deterministic row applied to the actual fresh-noise vector at update k+1. -/
noncomputable def tdLinearRowIncrement (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T k : ℕ) (hk : k < T)
    (V₀ : State → ℝ) (u : State → ℝ) (data : TDSamples State T) : ℝ :=
  ∑ s, u s * tdRowIncrement M π η T k hk V₀ s data

/-- Diagonal and off-diagonal actual conditional moments in one formula. -/
theorem tdRowIncrement_condExp_pair (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T k : ℕ) (hk : k < T) (V₀ : State → ℝ) (s r : State) :
    (tdSamplingLaw M π T)[(fun data ↦ tdRowIncrement M π η T k hk V₀ s data *
      tdRowIncrement M π η T k hk V₀ r data) | tdPastSigma T k] =ᵐ[tdSamplingLaw M π T]
      fun data ↦ if s = r then (M.policyTransition π s).variance (tdValueBefore M π η T k V₀ data) else 0 := by
  classical
  by_cases he : s = r
  · subst r
    have hh := tdRowIncrement_condExp_sq M π η T k hk V₀ s
    simpa only [← pow_two, if_pos rfl] using hh
  · simpa only [tdCrossRowNoise, if_neg he] using tdRowIncrement_condExp_cross M π η T k hk V₀ s r he

/-- The exact conditional second moment has SQUARED row coefficients; no
nonnegative-row inequality is used to disguise this identity. -/
theorem tdLinearRowIncrement_condExp_sq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T k : ℕ) (hk : k < T) (V₀ : State → ℝ) (u : State → ℝ) :
    (tdSamplingLaw M π T)[(fun data ↦ tdLinearRowIncrement M π η T k hk V₀ u data ^ 2) | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun data ↦
        ∑ s, u s ^ 2 * (M.policyTransition π s).variance (tdValueBefore M π η T k V₀ data) := by
  classical
  let ξ (s : State) := tdRowIncrement M π η T k hk V₀ s
  let f (z : State × State) : TDSamples State T → ℝ := fun data ↦
    (u z.1 * u z.2) * (ξ z.1 data * ξ z.2 data)
  have he : (fun data ↦ tdLinearRowIncrement M π η T k hk V₀ u data ^ 2) = ∑ z, f z := by
    funext data
    simp only [tdLinearRowIncrement, pow_two, Fintype.sum_mul_sum, Fintype.sum_prod_type, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [f, ξ]
    ring
  rw [he]
  have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
    (f := f) (fun z hz ↦ tdSampling_integrable M π T _) (tdPastSigma T k)
  have hterm (z : State × State) : (tdSamplingLaw M π T)[f z | tdPastSigma T k] =ᵐ[tdSamplingLaw M π T]
      fun data ↦ (u z.1 * u z.2) * (if z.1 = z.2 then
        (M.policyTransition π z.1).variance (tdValueBefore M π η T k V₀ data) else 0) := by
    have hc := condExp_smul (μ := tdSamplingLaw M π T) (u z.1 * u z.2)
      (fun data ↦ ξ z.1 data * ξ z.2 data) (tdPastSigma T k)
    filter_upwards [hc, tdRowIncrement_condExp_pair M π η T k hk V₀ z.1 z.2] with data hd hp
    simpa only [f, ξ, Pi.smul_apply, smul_eq_mul, hp] using hd
  filter_upwards [hsum, ae_all_iff.mpr hterm] with data hd hterms
  rw [hd]
  simp only [Finset.sum_apply]
  calc
    _ = ∑ z : State × State, (u z.1 * u z.2) * (if z.1 = z.2 then
        (M.policyTransition π z.1).variance (tdValueBefore M π η T k V₀ data) else 0) :=
      Finset.sum_congr rfl (fun z hz ↦ hterms z)
    _ = _ := by simp [Fintype.sum_prod_type, pow_two]

/-- Source nonnegative-row coefficient inequality, before any model bound. -/
theorem td_nonnegative_row_variance_proxy (u v : State → ℝ)
    (hu : ∀ s, 0 ≤ u s) (hv : ∀ s, 0 ≤ v s) :
    (∑ s, u s ^ 2 * v s) ≤ (∑ s, u s) * ∑ s, u s * v s := by
  calc
    _ ≤ ∑ s, (∑ r, u r) * (u s * v s) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsingle : u s ≤ ∑ r, u r := Finset.single_le_sum (fun r hr ↦ hu r) (Finset.mem_univ s)
      have hh := mul_le_mul_of_nonneg_right hsingle (mul_nonneg (hu s) (hv s))
      nlinarith
    _ = _ := by rw [Finset.mul_sum]

/-- The source row-mass variance proxy is proved from the exact conditional
squared-coefficient identity and actual true-row variance nonnegativity. -/
theorem tdLinearRowIncrement_condExp_sq_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T k : ℕ) (hk : k < T) (V₀ : State → ℝ) (u : State → ℝ) (hu : ∀ s, 0 ≤ u s) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      (tdSamplingLaw M π T)[(fun data ↦ tdLinearRowIncrement M π η T k hk V₀ u data ^ 2) | tdPastSigma T k] data ≤
        (∑ s, u s) * ∑ s, u s * (M.policyTransition π s).variance (tdValueBefore M π η T k V₀ data) := by
  filter_upwards [tdLinearRowIncrement_condExp_sq M π η T k hk V₀ u] with data hd
  rw [hd]
  exact td_nonnegative_row_variance_proxy u _ hu (fun s ↦ (M.policyTransition π s).variance_nonneg _)

/- To consume this for the source Z^(τ) at update k+1≤τ≤T, derive u from
γη_(k+1) times the ACTUAL chronological propagator row, prove its representation,
nonnegativity and row mass (the exact time-weight product), then specialize.
The source late-terminal regime is needed for the later small uniform caps,
not for this exact generic conditional identity. No such representation or
variance cap is a premise of the eventual algorithm theorem. -/
end StatisticalRL.TemporalDifference
