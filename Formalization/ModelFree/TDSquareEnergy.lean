import Formalization.ModelFree.TDConditionalMoments

/-! Source Lemma `lemma:TD-square`, `eq:TD-square-energy`.
Conditional squared-iterate energy under the actual finite sampling law. -/
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSquareEnergyStateMeasurable : MeasurableSpace State := ⊤

/-- Fresh predictable square moments under the actual synchronous product law.
This is the row expectation of the squared predictable function at the actual
coordinate `(s,t+1)`, conditional on the used-sample prefix through time t. -/
theorem tdFresh_predictable_square_condExp
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T t : ℕ) (ht : t < T) (s : State)
    (g : State → TDSamples State T → ℝ)
    (hg : ∀ x, StronglyMeasurable[tdPastSigma T t] (g x)) :
    (tdSamplingLaw M π T)[(fun data ↦
      g (data (s,⟨t+1,by omega⟩)) data ^ 2) | tdPastSigma T t]
      =ᵐ[tdSamplingLaw M π T] fun data ↦
        (M.policyTransition π s).expectation (fun x ↦ g x data ^ 2) := by
  classical
  let c : State → TDSamples State T → ℝ := fun x data ↦ g x data ^ 2
  have hc : ∀ x, StronglyMeasurable[tdPastSigma T t] (c x) := fun x ↦ (hg x).pow 2
  have he : (fun data : TDSamples State T ↦
      g (data (s,⟨t+1,by omega⟩)) data ^ 2) =
      ∑ x, c x * tdFreshIndicator T t ht s x := by
    funext data
    simp [c, tdFreshIndicator]
  rw [he]
  have h := tdFresh_predictable_sum_condExp M π T t ht s c hc
  filter_upwards [h] with data hd
  simpa [c, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd

/-- The pathwise interval for TD iterates only needs source rates at positive
indices. The existing generic interval helper mentions eta(0), although the
recurrence never uses it, so this wrapper replaces that unused value by zero. -/
theorem tdIterate_bounds_of_positive_rates
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → State) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (t : ℕ) (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (s : State) :
    0 ≤ tdIterate M π η samples V₀ t s ∧
      tdIterate M π η samples V₀ t s ≤ M.effectiveHorizon := by
  let η₀ : ℕ → ℝ := fun i ↦ if i = 0 then 0 else η i
  have hη₀ : ∀ i, i ≤ t → 0 ≤ η₀ i ∧ η₀ i ≤ 1 := by
    intro i hi
    by_cases hzero : i = 0
    · simp [η₀, hzero]
    · have hpos : 1 ≤ i := by omega
      simpa [η₀, hzero] using hη i hpos hi
  have hiter (n : ℕ) : tdIterate M π η₀ samples V₀ n = tdIterate M π η samples V₀ n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      funext x
      simp [tdIterate, η₀, ih]
  rw [← hiter t]
  exact tdIterate_bounds M π η₀ samples V₀ h₀ t hη₀ s

/-- The one-step squared-iterate inequality from source
`eq:TD-square-energy`, expressed under the actual finite sampling law.
The conditioning sigma-algebra contains source sample times 1,...,k−1 and
the fresh update uses coordinate k. In particular, eta(0) is unconstrained. -/
theorem tdSquaredIterateEnergy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) :
    ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      η k * (1 - η k) * M.discount ^ 2 *
          (M.policyTransition π s).variance (tdValueBefore M π η T (k - 1) V₀ data)
        ≤ (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s ^ 2
          + η k * M.discount *
            (M.policyTransition π s).expectation
              (fun x ↦ tdValueBefore M π η T (k - 1) V₀ data x ^ 2)
          - (tdSamplingLaw M π T)[(fun data ↦
              tdValueBefore M π η T k V₀ data s ^ 2) | tdPastSigma T (k - 1)] data
          + 2 * η k / (1 - M.discount) := by
  classical
  let v : TDSamples State T → State → ℝ := fun data ↦
    tdValueBefore M π η T (k - 1) V₀ data
  let fresh : State → TDSamples State T → ℝ := fun s data ↦
    v data (data (s,⟨k,by omega⟩))
  let target : State → TDSamples State T → ℝ := fun s data ↦
    policyReward M π s + M.discount * fresh s data
  let residual : State → TDSamples State T → ℝ := fun s data ↦
    target s data - v data s
  let targetSquareCond (s : State) : TDSamples State T → ℝ := fun data ↦
    (tdSamplingLaw M π T)[(fun d ↦ target s d ^ 2) | tdPastSigma T (k - 1)] data
  let residualSquareCond (s : State) : TDSamples State T → ℝ := fun data ↦
    (tdSamplingLaw M π T)[(fun d ↦ residual s d ^ 2) | tdPastSigma T (k - 1)] data
  let nextSquareCond (s : State) : TDSamples State T → ℝ := fun data ↦
    (tdSamplingLaw M π T)[(fun d ↦ tdValueBefore M π η T k V₀ d s ^ 2) |
      tdPastSigma T (k - 1)] data

  have hηk := hη k hk hkT
  have hγ₁ : M.discount ≤ 1 := M.discount_lt_one.le
  have hV : ∀ data s, 0 ≤ v data s ∧ v data s ≤ M.effectiveHorizon := by
    intro data s
    exact tdIterate_bounds_of_positive_rates M π η (tdSamplesExtend M T data) V₀ h₀
      (k - 1) (fun i hi1 hiT ↦ hη i hi1 (by omega)) s

  have hupdate (data : TDSamples State T) (s : State) :
      tdValueBefore M π η T k V₀ data s =
        (1 - η k) * v data s + η k * target s data := by
    have hkrec : (k - 1) + 1 = k := by omega
    have hklt : k < T + 1 := by omega
    rw [← hkrec]
    simp [tdValueBefore, tdIterate, v, target, fresh, tdSamplesExtend, hklt, hkrec]

  have htarget_meas (s x : State) :
      StronglyMeasurable[tdPastSigma T (k - 1)]
        (fun data ↦ policyReward M π s + M.discount * v data x) := by
    exact stronglyMeasurable_const.add
      (stronglyMeasurable_const.mul
        (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ x))
  have hresidual_meas (s x : State) :
      StronglyMeasurable[tdPastSigma T (k - 1)]
        (fun data ↦ policyReward M π s + M.discount * v data x - v data s) := by
    exact (htarget_meas s x).sub
      (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ s)

  have htargetFormula (s : State) :
      (tdSamplingLaw M π T)[(fun data ↦ target s data ^ 2) | tdPastSigma T (k - 1)]
        =ᵐ[tdSamplingLaw M π T] fun data ↦
          (M.policyTransition π s).expectation
            (fun x ↦ (policyReward M π s + M.discount * v data x) ^ 2) := by
    simpa [target, fresh, Nat.sub_add_cancel hk] using
      tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
        (fun x data ↦ policyReward M π s + M.discount * v data x) (htarget_meas s)

  have hresidualFormula (s : State) :
      (tdSamplingLaw M π T)[(fun data ↦ residual s data ^ 2) | tdPastSigma T (k - 1)]
        =ᵐ[tdSamplingLaw M π T] fun data ↦
          (M.policyTransition π s).expectation
            (fun x ↦ (policyReward M π s + M.discount * v data x - v data s) ^ 2) := by
    simpa [residual, target, fresh, Nat.sub_add_cancel hk] using
      tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
        (fun x data ↦ policyReward M π s + M.discount * v data x - v data s)
        (hresidual_meas s)

  let updateAtFresh (s x : State) (data : TDSamples State T) : ℝ :=
    (1 - η k) * v data s + η k * (policyReward M π s + M.discount * v data x)
  have hupdateAtFresh_meas (s x : State) :
      StronglyMeasurable[tdPastSigma T (k - 1)] (fun data ↦ updateAtFresh s x data) := by
    exact (stronglyMeasurable_const.mul
        (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ s)).add
      (stronglyMeasurable_const.mul
        (stronglyMeasurable_const.add
          (stronglyMeasurable_const.mul
            (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ x))))

  have hnextFresh (s : State) :
      (tdSamplingLaw M π T)[(fun data ↦ tdValueBefore M π η T k V₀ data s ^ 2) |
          tdPastSigma T (k - 1)]
        =ᵐ[tdSamplingLaw M π T] fun data ↦
          (M.policyTransition π s).expectation (fun x ↦ updateAtFresh s x data ^ 2) := by
    have hfun : (fun data : TDSamples State T ↦
        tdValueBefore M π η T k V₀ data s ^ 2) =
        (fun data ↦ updateAtFresh s (data (s,⟨k,by omega⟩)) data ^ 2) := by
      funext data
      rw [hupdate data s]
    rw [hfun]
    simpa [Nat.sub_add_cancel hk] using
      tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
        (fun x data ↦ updateAtFresh s x data) (hupdateAtFresh_meas s)

  have hnextFormula (s : State) :
      nextSquareCond s =ᵐ[tdSamplingLaw M π T] fun data ↦
        (1 - η k) * v data s ^ 2 + η k * targetSquareCond s data
          - η k * (1 - η k) * residualSquareCond s data := by
    have hrow (data : TDSamples State T) :
        (M.policyTransition π s).expectation (fun x ↦ updateAtFresh s x data ^ 2) =
          (1 - η k) * v data s ^ 2
            + η k * (M.policyTransition π s).expectation
                (fun x ↦ (policyReward M π s + M.discount * v data x) ^ 2)
            - η k * (1 - η k) * (M.policyTransition π s).expectation
                (fun x ↦ (policyReward M π s + M.discount * v data x - v data s) ^ 2) := by
      let d := M.policyTransition π s
      have hpoint (x : State) :
          updateAtFresh s x data ^ 2 =
            (1 - η k) * v data s ^ 2
              + η k * (policyReward M π s + M.discount * v data x) ^ 2
              - η k * (1 - η k) *
                  (policyReward M π s + M.discount * v data x - v data s) ^ 2 := by
        dsimp [updateAtFresh]
        ring
      have hfun : (fun x ↦ updateAtFresh s x data ^ 2) =
          (fun x ↦ (1 - η k) * v data s ^ 2
            + η k * (policyReward M π s + M.discount * v data x) ^ 2
            - η k * (1 - η k) *
                (policyReward M π s + M.discount * v data x - v data s) ^ 2) := by
        funext x
        exact hpoint x
      rw [hfun]
      simp only [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_add,
        FiniteDistribution.expectation_const, FiniteDistribution.expectation_mul]
    filter_upwards [hnextFresh s, htargetFormula s, hresidualFormula s] with data hn ht hr
    change nextSquareCond s data = _ at hn
    change targetSquareCond s data = _ at ht
    change residualSquareCond s data = _ at hr
    rw [hn, ht, hr]
    exact hrow data

  have htargetBound (s : State) :
      ∀ᵐ data ∂tdSamplingLaw M π T,
        targetSquareCond s data ≤ M.discount *
          (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2)
          + 2 / (1 - M.discount) := by
    filter_upwards [htargetFormula s] with data hformula
    have hr := policyReward_bounds M π s
    have hv := hV data
    have hmean0 : 0 ≤ (M.policyTransition π s).expectation (v data) :=
      (M.policyTransition π s).expectation_nonneg (fun x ↦ (hv x).1)
    have hmeanH : (M.policyTransition π s).expectation (v data) ≤ M.effectiveHorizon :=
      (M.policyTransition π s).expectation_le_const (fun x ↦ (hv x).2)
    have hsecond0 : 0 ≤ (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2) :=
      (M.policyTransition π s).expectation_nonneg (fun x ↦ sq_nonneg (v data x))
    have hsecondMoment :
        (M.policyTransition π s).expectation
            (fun x ↦ (policyReward M π s + M.discount * v data x) ^ 2) =
          (policyReward M π s) ^ 2
            + 2 * policyReward M π s * M.discount *
                (M.policyTransition π s).expectation (v data)
            + M.discount ^ 2 *
                (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2) := by
      have hfun : (fun x ↦ (policyReward M π s + M.discount * v data x) ^ 2) =
          (fun x ↦ (policyReward M π s) ^ 2
            + (2 * policyReward M π s * M.discount) * v data x
            + M.discount ^ 2 * v data x ^ 2) := by
        funext x
        ring
      rw [hfun]
      simp only [FiniteDistribution.expectation_add, FiniteDistribution.expectation_mul,
        FiniteDistribution.expectation_const]
    have hγsq : M.discount ^ 2 ≤ M.discount := by
      have hgap := sub_nonneg.mpr hγ₁
      nlinarith [mul_nonneg M.discount_nonneg hgap]
    have hrγ : policyReward M π s * M.discount ≤ M.discount := by
      simpa using mul_le_mul_of_nonneg_right hr.2 M.discount_nonneg
    have hcross : (policyReward M π s * M.discount) *
        (M.policyTransition π s).expectation (v data) ≤
        M.discount * M.effectiveHorizon := by
      calc
        _ ≤ M.discount * (M.policyTransition π s).expectation (v data) :=
          mul_le_mul_of_nonneg_right hrγ hmean0
        _ ≤ M.discount * M.effectiveHorizon :=
          mul_le_mul_of_nonneg_left hmeanH M.discount_nonneg
    have hsmall : 1 + 2 * M.discount * M.effectiveHorizon ≤
        2 * M.effectiveHorizon := by
      have hrec := M.effectiveHorizon_recursion
      calc
        1 + 2 * M.discount * M.effectiveHorizon =
            M.effectiveHorizon + M.discount * M.effectiveHorizon := by linarith
        _ ≤ M.effectiveHorizon + M.effectiveHorizon := by
          nlinarith [mul_le_mul_of_nonneg_right hγ₁ M.effectiveHorizon_nonneg]
        _ = 2 * M.effectiveHorizon := by ring
    have hrow :
        (M.policyTransition π s).expectation
            (fun x ↦ (policyReward M π s + M.discount * v data x) ^ 2) ≤
          M.discount * (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2)
            + 2 * M.effectiveHorizon := by
      rw [hsecondMoment]
      have hcross' : 2 * policyReward M π s * M.discount *
          (M.policyTransition π s).expectation (v data) ≤
          2 * M.discount * M.effectiveHorizon := by
        nlinarith [hcross]
      have hquad : M.discount ^ 2 *
          (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2) ≤
          M.discount * (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2) :=
        mul_le_mul_of_nonneg_right hγsq hsecond0
      have hrSq : (policyReward M π s) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
      linarith
    have hH : M.effectiveHorizon = 1 / (1 - M.discount) := rfl
    calc
      targetSquareCond s data =
          (M.policyTransition π s).expectation
            (fun x ↦ (policyReward M π s + M.discount * v data x) ^ 2) := hformula
      _ ≤ M.discount * (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2)
            + 2 * M.effectiveHorizon := hrow
      _ = M.discount * (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2)
            + 2 / (1 - M.discount) := by
        congr 1
        calc
          2 * M.effectiveHorizon = 2 * (1 / (1 - M.discount)) := by rw [hH]
          _ = 2 / (1 - M.discount) := by ring

  have hresidualBound (s : State) :
      ∀ᵐ data ∂tdSamplingLaw M π T,
        M.discount ^ 2 * (M.policyTransition π s).variance (v data)
          ≤ residualSquareCond s data := by
    filter_upwards [hresidualFormula s] with data hformula
    let d := M.policyTransition π s
    let f : State → ℝ := fun x ↦ policyReward M π s + M.discount * v data x
    let center := v data s
    have hvarShift (g : State → ℝ) (c : ℝ) :
        d.variance (fun x ↦ g x - c) = d.variance g := by
      have hsq : (fun x ↦ (g x - c) ^ 2) =
          (fun x ↦ g x ^ 2 - 2 * c * g x + c ^ 2) := by
        funext x
        ring
      unfold FiniteDistribution.variance
      rw [hsq]
      simp only [d.expectation_sub, d.expectation_add, d.expectation_mul,
        d.expectation_const]
      ring_nf
    have hvarAffine : d.variance f = M.discount ^ 2 * d.variance (v data) := by
      have hsq : (fun x ↦ f x ^ 2) = fun x ↦
          (policyReward M π s) ^ 2
            + (2 * policyReward M π s * M.discount) * v data x
            + M.discount ^ 2 * (v data x) ^ 2 := by
        funext x
        simp only [f]
        ring
      have hmean : d.expectation f =
          policyReward M π s + M.discount * d.expectation (v data) := by
        simp only [f, d.expectation_add, d.expectation_mul, d.expectation_const]
      unfold FiniteDistribution.variance
      rw [hsq]
      simp only [d.expectation_add, d.expectation_mul, d.expectation_const]
      rw [hmean]
      ring_nf
    have hshiftLower := d.variance_le_expectation_sq (fun x ↦ f x - center)
    have hvarianceLower : M.discount ^ 2 * d.variance (v data) ≤
        d.expectation (fun x ↦ (f x - center) ^ 2) := by
      rw [← hvarAffine, ← hvarShift f center]
      exact hshiftLower
    calc
      M.discount ^ 2 * (M.policyTransition π s).variance (v data) =
          M.discount ^ 2 * d.variance (v data) := by rfl
      _ ≤ d.expectation (fun x ↦ (f x - center) ^ 2) := hvarianceLower
      _ = residualSquareCond s data := by
        simpa [residualSquareCond, residual, target, fresh, v, d, f, center] using
          hformula.symm

  filter_upwards [ae_all_iff.mpr hnextFormula,
    ae_all_iff.mpr htargetBound, ae_all_iff.mpr hresidualBound] with data hm ht hr
  intro s
  have hH : M.effectiveHorizon = 1 / (1 - M.discount) := rfl
  have hUpdate := hm s
  have hTarg := ht s
  have hRes := hr s
  have hηprod : 0 ≤ η k * (1 - η k) :=
    mul_nonneg hηk.1 (sub_nonneg.mpr hηk.2)
  change (tdSamplingLaw M π T)[(fun d ↦
      tdValueBefore M π η T k V₀ d s ^ 2) | tdPastSigma T (k - 1)] data = _ at hUpdate
  change (tdSamplingLaw M π T)[(fun d ↦ target s d ^ 2) | tdPastSigma T (k - 1)] data ≤ _ at hTarg
  change _ ≤ (tdSamplingLaw M π T)[(fun d ↦ residual s d ^ 2) | tdPastSigma T (k - 1)] data at hRes
  have htwoH : 2 / (1 - M.discount) = 2 * M.effectiveHorizon := by
    calc
      2 / (1 - M.discount) = 2 * (1 / (1 - M.discount)) := by ring
      _ = 2 * M.effectiveHorizon := by rw [← hH]
  rw [htwoH] at hTarg
  have hdiv : 2 * η k / (1 - M.discount) = 2 * η k * M.effectiveHorizon := by
    rw [DiscountedMDP.effectiveHorizon]
    ring
  rw [hdiv, hUpdate]
  have htargetGap : 0 ≤ M.discount *
      (M.policyTransition π s).expectation (fun x ↦ v data x ^ 2)
        + 2 * M.effectiveHorizon - targetSquareCond s data := by
    linarith
  have hresidualGap : 0 ≤ residualSquareCond s data -
      M.discount ^ 2 * (M.policyTransition π s).variance (v data) := by
    linarith
  have hfirst := mul_nonneg hηk.1 htargetGap
  have hsecond := mul_nonneg hηprod hresidualGap
  nlinarith [hfirst, hsecond]

end StatisticalRL.TemporalDifference
