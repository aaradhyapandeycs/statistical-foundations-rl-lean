import Formalization.ModelFree.TDSharpVariance
import Formalization.ModelFree.TDVariancePairwise
import Formalization.ModelFree.TDSquareEnergy

/-! Single-state square variance under the actual synchronous TD sample law and strict used prefix. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpFreshBridgeStateMeasurable : MeasurableSpace State := ⊤

/-- Conditional mean of the actual square update, expressed by the true policy
row on the fresh next-state coordinate. -/
noncomputable def tdSquareFreshRowMean (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s : State) (data : TDSamples State T) : ℝ :=
  (M.policyTransition π s).expectation
    (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data ^ 2)

/-- The actual update at source time `k` is the fresh-state map evaluated at
the actual array coordinate `(s,k)`. -/
theorem tdValueBefore_eq_tdSquareFreshUpdate
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (s : State) (data : TDSamples State T) :
    tdValueBefore M π η T k V₀ data s =
      tdSquareFreshUpdate M π η T V₀ k s (data (s,⟨k,by omega⟩)) data := by
  cases k with
  | zero => omega
  | succ n =>
    have hsample : tdSamplesExtend M T data (n + 1) s =
        data (s,⟨n + 1,by omega⟩) := by
      simp [tdSamplesExtend, show n + 1 < T + 1 by omega]
    simp only [tdValueBefore, tdSquareFreshUpdate, tdIterate,
      Nat.succ_sub_one]
    rw [hsample]

theorem tdSquareObservation_eq_freshSquare
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (s : State) :
    tdSquareObservation M π η T V₀ k s = fun data ↦
      tdSquareFreshUpdate M π η T V₀ k s (data (s,⟨k,by omega⟩)) data ^ 2 := by
  funext data
  simp only [tdSquareObservation, tdValueBefore_eq_tdSquareFreshUpdate M π η T V₀ k hk hkT s data]

/-- Exact conditional second moment of the centered square: it is the variance
of the squared fresh update under the true policy transition row. -/
theorem tdSquareCenteredConditionalSecondMoment_eq_rowVariance
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (s : State) :
    tdSquareCenteredConditionalSecondMoment M π η T V₀ k s =ᵐ[tdSamplingLaw M π T]
      fun data ↦ tdSquareFreshRowVariance M π η T V₀ k s data := by
  classical
  let past := tdPastSigma (State := State) T (k - 1)
  let rowMean := tdSquareFreshRowMean M π η T V₀ k s
  let centeredFresh (x : State) (data : TDSamples State T) :=
    tdSquareFreshUpdate M π η T V₀ k s x data ^ 2 - rowMean data
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
  have hrowMeanMeas : StronglyMeasurable[past] rowMean := by
    dsimp [rowMean, tdSquareFreshRowMean, FiniteDistribution.expectation]
    exact Finset.stronglyMeasurable_fun_sum _ fun x hx ↦
      stronglyMeasurable_const.mul ((hUmeas x).pow 2)
  have hcenteredMeas (x : State) :
      StronglyMeasurable[past] (fun data ↦ centeredFresh x data) := by
    exact (hUmeas x).pow 2 |>.sub hrowMeanMeas
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
    simpa [rowMean, tdSquareFreshRowMean, Nat.sub_add_cancel hk] using
      tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
        (fun x data ↦ tdSquareFreshUpdate M π η T V₀ k s x data) hUmeas
  have hmean :
      (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s | past] =ᵐ[tdSamplingLaw M π T]
        rowMean := by
    exact (condExp_congr_ae hobsAE).trans hmeanFresh
  have hcenter :
      tdSquareCentered M π η T V₀ k s =ᵐ[tdSamplingLaw M π T]
        fun data ↦ centeredFresh (data (s,⟨k,by omega⟩)) data := by
    filter_upwards [hmean] with data hm
    change tdSquareObservation M π η T V₀ k s data -
        (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s | past] data = _
    rw [hm, congrFun hobs data]
  have hcenterSquare :
      (fun data ↦ tdSquareCentered M π η T V₀ k s data ^ 2) =ᵐ[tdSamplingLaw M π T]
        fun data ↦ centeredFresh (data (s,⟨k,by omega⟩)) data ^ 2 := by
    filter_upwards [hcenter] with data hc
    simp [hc]
  have hsecondFresh :
      (tdSamplingLaw M π T)[(fun data ↦
        centeredFresh (data (s,⟨k,by omega⟩)) data ^ 2) | past] =ᵐ[tdSamplingLaw M π T]
        fun data ↦ (M.policyTransition π s).expectation
          (fun x ↦ centeredFresh x data ^ 2) := by
    simpa [Nat.sub_add_cancel hk] using
      tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
        centeredFresh hcenteredMeas
  have hsecond := (condExp_congr_ae hcenterSquare).trans hsecondFresh
  have hvariance :
      (fun data ↦ (M.policyTransition π s).expectation
        (fun x ↦ centeredFresh x data ^ 2)) =
      fun data ↦ tdSquareFreshRowVariance M π η T V₀ k s data := by
    funext data
    dsimp [centeredFresh, rowMean, tdSquareFreshRowVariance,
      tdSquareFreshRowMean]
    rw [FiniteDistribution.variance_eq_expectation_centered_sq]
  change (tdSamplingLaw M π T)[(fun data ↦
      tdSquareCentered M π η T V₀ k s data ^ 2) | past] =ᵐ[tdSamplingLaw M π T]
    fun data ↦ tdSquareFreshRowVariance M π η T V₀ k s data
  exact hsecond.trans (Filter.Eventually.of_forall fun data ↦ congrFun hvariance data)

/-- The actual conditional second moment is bounded by the square-Lipschitz
variance estimate on the true `Pπ(s,·)` row. Conditioning is on exactly the
used source prefix through `k−1`; `k=1` and `k=T` are included. -/
theorem tdSquareCenteredConditionalSecondMoment_le_rowVariance
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) (s : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdSquareCenteredConditionalSecondMoment M π η T V₀ k s data ≤
        4 * M.effectiveHorizon ^ 2 *
          (M.policyTransition π s).variance
            (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data) := by
  have hV : ∀ data x, 0 ≤ tdValueBefore M π η T (k - 1) V₀ data x ∧
      tdValueBefore M π η T (k - 1) V₀ data x ≤ M.effectiveHorizon := by
    intro data x
    exact tdIterate_bounds_of_positive_rates M π η (tdSamplesExtend M T data) V₀ h₀
      (k - 1) (fun i hi1 hiT ↦ hη i hi1 (by omega)) x
  have hηk := hη k hk hkT
  have hFreshRange (data : TDSamples State T) (x : State) :
      0 ≤ tdSquareFreshUpdate M π η T V₀ k s x data ∧
      tdSquareFreshUpdate M π η T V₀ k s x data ≤ M.effectiveHorizon := by
    have hv := hV data s
    have hvx := hV data x
    have hr := policyReward_bounds M π s
    have htarget :
        0 ≤ policyReward M π s + M.discount *
            tdValueBefore M π η T (k - 1) V₀ data x ∧
        policyReward M π s + M.discount *
            tdValueBefore M π η T (k - 1) V₀ data x ≤ M.effectiveHorizon := by
      constructor
      · exact add_nonneg hr.1 (mul_nonneg M.discount_nonneg hvx.1)
      · calc
          _ ≤ 1 + M.discount * M.effectiveHorizon :=
            add_le_add hr.2 (mul_le_mul_of_nonneg_left hvx.2 M.discount_nonneg)
          _ = M.effectiveHorizon := M.effectiveHorizon_recursion
    constructor
    · exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hηk.2) hv.1)
        (mul_nonneg hηk.1 htarget.1)
    · change (1 - η k) *
          tdValueBefore M π η T (k - 1) V₀ data s +
          η k * (policyReward M π s + M.discount *
            tdValueBefore M π η T (k - 1) V₀ data x) ≤ M.effectiveHorizon
      nlinarith [mul_nonneg (sub_nonneg.mpr hηk.2)
          (sub_nonneg.mpr hv.2),
        mul_nonneg hηk.1 (sub_nonneg.mpr htarget.2)]
  have hEq := tdSquareCenteredConditionalSecondMoment_eq_rowVariance
    M π η T V₀ k hk hkT s
  filter_upwards [hEq] with data hdata
  rw [hdata]
  exact FiniteDistribution.variance_sq_le_four_mul_sq
    (M.policyTransition π s)
    (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data)
    M.effectiveHorizon_nonneg (hFreshRange data)

/-- Affine variance for the actual fresh update. Together with the preceding
conditional square bound this recovers the source `η_k²γ² Var_{Pπ}(V_{k−1})`
factor, with no full-support assumption on the true row. -/
theorem variance_affine_finiteDistribution
    (d : FiniteDistribution State) (a b : ℝ) (v : State → ℝ) :
    d.variance (fun x ↦ a + b * v x) = b ^ 2 * d.variance v := by
  rw [FiniteDistribution.variance_eq_pairwiseVarianceExpression,
    FiniteDistribution.variance_eq_pairwiseVarianceExpression]
  unfold FiniteDistribution.pairwiseVarianceExpression
  have hdouble :
      (∑ x, ∑ y, d.prob x * d.prob y *
        ((a + b * v x) - (a + b * v y)) ^ 2) =
        b ^ 2 * (∑ x, ∑ y, d.prob x * d.prob y * (v x - v y) ^ 2) := by
    calc
      _ = ∑ x, ∑ y, b ^ 2 *
          (d.prob x * d.prob y * (v x - v y) ^ 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by
        calc
          _ = ∑ x, b ^ 2 *
              (∑ y, d.prob x * d.prob y * (v x - v y) ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
          _ = _ := by rw [Finset.mul_sum]
  rw [hdouble]
  ring

/-- The true transition-row variance of the fresh update is exactly the source
affine-update variance, for each old sample prefix. -/
theorem tdSquareFreshUpdate_variance_eq_oldRow
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (s : State) (data : TDSamples State T) :
    (M.policyTransition π s).variance
        (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data) =
      (η k * M.discount) ^ 2 *
        (M.policyTransition π s).variance
          (tdValueBefore M π η T (k - 1) V₀ data) := by
  let a := (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s +
    η k * policyReward M π s
  have hfun : (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data) =
      fun x ↦ a + (η k * M.discount) *
        tdValueBefore M π η T (k - 1) V₀ data x := by
    funext x
    dsimp [a, tdSquareFreshUpdate]
    ring
  rw [hfun, variance_affine_finiteDistribution]

/-! The distinct-state conditional covariance
`E_{k-1}[C_k(s)C_k(r)]=0` is deliberately not proved here. It requires a
square-specific double fresh-indicator expansion using the actual distinct
coordinates `(s,k)` and `(r,k)`, followed by `tdFreshIndicators_condExp_mul`.
The raw-noise cross-covariance theorem alone does not supply it. -/

end StatisticalRL.TemporalDifference
