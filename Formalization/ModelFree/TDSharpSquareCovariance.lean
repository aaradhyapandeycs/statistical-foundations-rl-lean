import Formalization.ModelFree.TDSharpFreshVarianceBridge
import Formalization.ModelFree.TDCrossCovariance

/-! Square-specific conditional cross-state covariance under the actual synchronous sampling law and strict used prefix. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpSquareCovarianceStateMeasurable : MeasurableSpace State := ⊤

/-- Square-valued fresh observation centered by its true policy-row mean.
Every coefficient is a function of the strict past; only the indicator at
the current fresh source-time coordinate depends on the new draw. -/
noncomputable def tdSquareFreshCentered
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ) (s x : State)
    (data : TDSamples State T) : ℝ :=
  tdSquareFreshUpdate M π η T V₀ k s x data ^ 2 -
    tdSquareFreshRowMean M π η T V₀ k s data

/-- The actual centered-square observation equals the predictable centered
coefficient selected by the fresh coordinate, almost surely. -/
theorem tdSquareCentered_eq_freshCentered
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (s : State) :
    tdSquareCentered M π η T V₀ k s =ᵐ[tdSamplingLaw M π T]
      fun data ↦ tdSquareFreshCentered M π η T V₀ k s
        (data (s,⟨k,by omega⟩)) data := by
  classical
  let past := tdPastSigma (State := State) T (k - 1)
  let rowMean := tdSquareFreshRowMean M π η T V₀ k s
  have hUmeas (x : State) :
      StronglyMeasurable[past]
        (fun data ↦ tdSquareFreshUpdate M π η T V₀ k s x data) := by
    dsimp [tdSquareFreshUpdate]
    exact (stronglyMeasurable_const.mul
        (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ s)).add
      (stronglyMeasurable_const.mul
        (stronglyMeasurable_const.add
          (stronglyMeasurable_const.mul
            (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ x))))
  have hobs :
      tdSquareObservation M π η T V₀ k s = fun data ↦
        tdSquareFreshUpdate M π η T V₀ k s
          (data (s,⟨k,by omega⟩)) data ^ 2 :=
    tdSquareObservation_eq_freshSquare M π η T V₀ k hk hkT s
  have hobsAE : tdSquareObservation M π η T V₀ k s =ᵐ[tdSamplingLaw M π T]
      (fun data ↦ tdSquareFreshUpdate M π η T V₀ k s
        (data (s,⟨k,by omega⟩)) data ^ 2) :=
    Filter.Eventually.of_forall fun data ↦ congrFun hobs data
  have hmeanFresh :
      (tdSamplingLaw M π T)[(fun data ↦ tdSquareFreshUpdate M π η T V₀ k s
        (data (s,⟨k,by omega⟩)) data ^ 2) | past] =ᵐ[tdSamplingLaw M π T]
        rowMean := by
    simpa [rowMean, Nat.sub_add_cancel hk] using
      tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
        (fun x data ↦ tdSquareFreshUpdate M π η T V₀ k s x data) hUmeas
  have hmean :
      (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s | past] =ᵐ[tdSamplingLaw M π T]
        rowMean := (condExp_congr_ae hobsAE).trans hmeanFresh
  filter_upwards [hmean] with data hm
  change tdSquareObservation M π η T V₀ k s data -
      (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s | past] data = _
  rw [hm, congrFun hobs data]
  rfl

/-- Predictable measurability of the true fresh centered-square coefficient. -/
theorem tdSquareFreshCentered_strongPast
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hkT : k ≤ T) (s x : State) :
    StronglyMeasurable[tdPastSigma T (k - 1)]
      (tdSquareFreshCentered M π η T V₀ k s x) := by
  have hU (z : State) : StronglyMeasurable[tdPastSigma T (k - 1)]
      (fun data ↦ tdSquareFreshUpdate M π η T V₀ k s z data) := by
    dsimp [tdSquareFreshUpdate]
    exact (stronglyMeasurable_const.mul
        (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ s)).add
      (stronglyMeasurable_const.mul
        (stronglyMeasurable_const.add
          (stronglyMeasurable_const.mul
            (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ z))))
  have hrow : StronglyMeasurable[tdPastSigma T (k - 1)]
      (fun data ↦ tdSquareFreshRowMean M π η T V₀ k s data) := by
    dsimp [tdSquareFreshRowMean, FiniteDistribution.expectation]
    exact Finset.stronglyMeasurable_fun_sum _ fun z hz ↦
      stronglyMeasurable_const.mul ((hU z).pow 2)
  change StronglyMeasurable[tdPastSigma T (k - 1)]
    (fun data ↦ tdSquareFreshUpdate M π η T V₀ k s x data ^ 2 -
      tdSquareFreshRowMean M π η T V₀ k s data)
  exact ((hU x).pow 2).sub hrow

/-- Two centered expectations under independent finite rows factor to zero,
with no positivity assumptions on individual atoms. -/
theorem tdSquare_centered_product_sum_eq_zero
    (p q : FiniteDistribution State) (f g : State → ℝ) :
    (∑ x, ∑ y, (f x - p.expectation f) * (g y - q.expectation g) *
      (p.prob x * q.prob y)) = 0 := by
  have hp : ∑ x, p.prob x * (f x - p.expectation f) = 0 := by
    change p.expectation (fun x ↦ f x - p.expectation f) = 0
    rw [p.expectation_sub, p.expectation_const]
    ring
  have hq : ∑ y, q.prob y * (g y - q.expectation g) = 0 := by
    change q.expectation (fun y ↦ g y - q.expectation g) = 0
    rw [q.expectation_sub, q.expectation_const]
    ring
  calc
    _ = (∑ x, p.prob x * (f x - p.expectation f)) *
        (∑ y, q.prob y * (g y - q.expectation g)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = 0 := by rw [hp, hq]; ring

/-- The product of the two fresh centered-square coefficients expands through
actual current-layer indicators at `(s,k)` and `(r,k)`. -/
theorem tdSquareFreshCentered_product_indicator_expansion
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (s r : State) (data : TDSamples State T) :
    tdSquareFreshCentered M π η T V₀ k s (data (s,⟨k,by omega⟩)) data *
      tdSquareFreshCentered M π η T V₀ k r (data (r,⟨k,by omega⟩)) data =
    ∑ x, ∑ y,
      (tdSquareFreshCentered M π η T V₀ k s x data *
        tdSquareFreshCentered M π η T V₀ k r y data) *
        (tdFreshIndicator T (k - 1) (by omega) s x data *
          tdFreshIndicator T (k - 1) (by omega) r y data) := by
  classical
  simp [tdSquareFreshCentered, tdFreshIndicator, Nat.sub_add_cancel hk]

/-- Distinct-state conditional covariance of centered-square observations is
zero under the actual joint sampling law, given the used prefix through `k-1`.
This square-specific fact is derived by a double indicator expansion and the
actual distinct-coordinate conditional product law. -/
theorem tdSquareCentered_condExp_cross_eq_zero
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (s r : State) (hsr : s ≠ r) :
    (tdSamplingLaw M π T)[(fun data ↦
      tdSquareCentered M π η T V₀ k s data *
        tdSquareCentered M π η T V₀ k r data) | tdPastSigma T (k - 1)]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  classical
  let past := tdPastSigma (State := State) T (k - 1)
  let c (x y : State) (data : TDSamples State T) :=
    tdSquareFreshCentered M π η T V₀ k s x data *
      tdSquareFreshCentered M π η T V₀ k r y data
  let J (x y : State) (data : TDSamples State T) :=
    tdFreshIndicator T (k - 1) (by omega) s x data *
      tdFreshIndicator T (k - 1) (by omega) r y data
  have hc (x y : State) : StronglyMeasurable[past] (c x y) := by
    dsimp [c]
    exact (tdSquareFreshCentered_strongPast M π η T V₀ k hkT s x).mul
      (tdSquareFreshCentered_strongPast M π η T V₀ k hkT r y)
  have hsCenter := tdSquareCentered_eq_freshCentered M π η T V₀ k hk hkT s
  have hrCenter := tdSquareCentered_eq_freshCentered M π η T V₀ k hk hkT r
  have hprodCenter :
      (fun data ↦ tdSquareCentered M π η T V₀ k s data *
        tdSquareCentered M π η T V₀ k r data) =ᵐ[tdSamplingLaw M π T]
      (fun data ↦ tdSquareFreshCentered M π η T V₀ k s
          (data (s,⟨k,by omega⟩)) data *
        tdSquareFreshCentered M π η T V₀ k r
          (data (r,⟨k,by omega⟩)) data) :=
    hsCenter.mul hrCenter
  have hExpansion :
      (fun data ↦ tdSquareFreshCentered M π η T V₀ k s
          (data (s,⟨k,by omega⟩)) data *
        tdSquareFreshCentered M π η T V₀ k r
          (data (r,⟨k,by omega⟩)) data) =
      (∑ z : State × State, c z.1 z.2 * J z.1 z.2) := by
    funext data
    simpa only [Fintype.sum_prod_type, Finset.sum_apply, Pi.mul_apply, c, J] using
      tdSquareFreshCentered_product_indicator_expansion
        M π η T V₀ k hk hkT s r data
  have hExpansionAE :
      (fun data ↦ tdSquareFreshCentered M π η T V₀ k s
          (data (s,⟨k,by omega⟩)) data *
        tdSquareFreshCentered M π η T V₀ k r
          (data (r,⟨k,by omega⟩)) data) =ᵐ[tdSamplingLaw M π T]
      (∑ z : State × State, c z.1 z.2 * J z.1 z.2) :=
    Filter.Eventually.of_forall fun data ↦ congrFun hExpansion data
  have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
    (f := fun z : State × State ↦ c z.1 z.2 * J z.1 z.2)
    (fun z hz ↦ tdSampling_integrable M π T _) past
  have hterms (x y : State) :
      (tdSamplingLaw M π T)[c x y * J x y | past] =ᵐ[tdSamplingLaw M π T]
        fun data ↦ c x y data *
          ((M.policyTransition π s).prob x * (M.policyTransition π r).prob y) := by
    have hcoeff :
        (tdSamplingLaw M π T)[c x y * J x y | past] =ᵐ[tdSamplingLaw M π T]
          fun data ↦ c x y data *
            (tdSamplingLaw M π T)[J x y | past] data := by
      exact condExp_mul_of_stronglyMeasurable_left (hc x y)
        (tdSampling_integrable M π T _) (tdSampling_integrable M π T _)
    have hind := tdFreshIndicators_condExp_mul M π T (k - 1) (by omega)
      s r x y hsr
    exact hcoeff.trans ((Filter.EventuallyEq.refl _ _).mul hind)
  have hzero (data : TDSamples State T) :
      (∑ x, ∑ y, c x y data *
        ((M.policyTransition π s).prob x * (M.policyTransition π r).prob y)) = 0 := by
    dsimp [c, tdSquareFreshCentered]
    simpa [tdSquareFreshRowMean] using
      tdSquare_centered_product_sum_eq_zero (M.policyTransition π s)
        (M.policyTransition π r)
        (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data ^ 2)
        (fun y ↦ tdSquareFreshUpdate M π η T V₀ k r y data ^ 2)
  have hcondExpanded :
      (tdSamplingLaw M π T)[
        (∑ z : State × State, c z.1 z.2 * J z.1 z.2) | past]
        =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
    have htermsAll := ae_all_iff.mpr (fun z : State × State ↦ hterms z.1 z.2)
    filter_upwards [hsum, htermsAll] with data hsumData htermsData
    rw [hsumData]
    simp only [Finset.sum_apply, Fintype.sum_prod_type]
    calc
      _ = ∑ x, ∑ y, c x y data *
          ((M.policyTransition π s).prob x * (M.policyTransition π r).prob y) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact htermsData (x, y)
      _ = 0 := hzero data
  have hfreshProduct :
      (tdSamplingLaw M π T)[(fun data ↦ tdSquareFreshCentered M π η T V₀ k s
          (data (s,⟨k,by omega⟩)) data *
        tdSquareFreshCentered M π η T V₀ k r
          (data (r,⟨k,by omega⟩)) data) | past]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 :=
    (condExp_congr_ae hExpansionAE).trans hcondExpanded
  exact (condExp_congr_ae hprodCenter).trans hfreshProduct

end StatisticalRL.TemporalDifference
