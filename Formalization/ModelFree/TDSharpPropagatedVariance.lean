import Formalization.ModelFree.TDSharpLateWindow
import Formalization.ModelFree.TDSharpSquareCovariance
import Formalization.ModelFree.TDPropagatorRows
import Formalization.ModelFree.TDLinearRowVariance

/-! FIXED-TERMINAL CONDITIONAL VARIANCE BRIDGE.

This module combines the single-state centered-square variance and the
square-specific off-diagonal covariance under the actual prefix, then applies
the actual chronological propagator row. The final theorem is only for the
source late window floor(t/2)+1 ≤ k ≤ t; it does not assert a whole-window
variance sum or a Freedman bound. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpPropVarianceStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance tdSharpPropVarianceStateDecidable : DecidableEq State := Classical.decEq State

/-- A deterministic row applied to the actual centered-square vector at
source update `k`. -/
noncomputable def tdSquareCenteredWeightedRow
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (u : State → ℝ) (data : TDSamples State T) : ℝ :=
  ∑ r, u r * tdSquareCentered M π η T V₀ k r data

/-- Exact conditional second moment of a deterministic weighted centered-square
row. Diagonal terms are the true fresh policy-row variances; off-diagonal
terms vanish by the square-specific distinct-coordinate theorem. -/
theorem tdSquareCenteredWeightedRow_condExp_sq_eq
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkT : k ≤ T) (u : State → ℝ) :
    (tdSamplingLaw M π T)[(fun data ↦
      tdSquareCenteredWeightedRow M π η T V₀ k u data ^ 2) | tdPastSigma T (k - 1)]
      =ᵐ[tdSamplingLaw M π T] fun data ↦
        ∑ r, u r ^ 2 * tdSquareFreshRowVariance M π η T V₀ k r data := by
  classical
  let ξ (r : State) : TDSamples State T → ℝ :=
    tdSquareCentered M π η T V₀ k r
  let f (z : State × State) : TDSamples State T → ℝ := fun data ↦
    (u z.1 * u z.2) * (ξ z.1 data * ξ z.2 data)
  have he : (fun data ↦ tdSquareCenteredWeightedRow M π η T V₀ k u data ^ 2) =
      ∑ z, f z := by
    funext data
    simp only [tdSquareCenteredWeightedRow, pow_two, Fintype.sum_mul_sum,
      Fintype.sum_prod_type, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [f, ξ]
    ring
  rw [he]
  have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
    (f := f) (fun z hz ↦ tdSampling_integrable M π T _) (tdPastSigma T (k - 1))
  have hpair (s r : State) :
      (tdSamplingLaw M π T)[ξ s * ξ r | tdPastSigma T (k - 1)]
        =ᵐ[tdSamplingLaw M π T] fun data ↦
          if s = r then tdSquareFreshRowVariance M π η T V₀ k s data else 0 := by
    by_cases hsr : s = r
    · subst r
      simpa only [← pow_two, if_pos rfl] using
        tdSquareCenteredConditionalSecondMoment_eq_rowVariance
          M π η T V₀ k hk hkT s
    · simpa only [if_neg hsr] using
        tdSquareCentered_condExp_cross_eq_zero M π η T V₀ k hk hkT s r hsr
  have hterm (z : State × State) :
      (tdSamplingLaw M π T)[f z | tdPastSigma T (k - 1)]
        =ᵐ[tdSamplingLaw M π T] fun data ↦
          (u z.1 * u z.2) * (if z.1 = z.2 then
            tdSquareFreshRowVariance M π η T V₀ k z.1 data else 0) := by
    have hc :
        (tdSamplingLaw M π T)[f z | tdPastSigma T (k - 1)]
          =ᵐ[tdSamplingLaw M π T] fun data ↦ (u z.1 * u z.2) *
            (tdSamplingLaw M π T)[ξ z.1 * ξ z.2 | tdPastSigma T (k - 1)] data := by
      simpa only [f, ξ, Pi.smul_apply, smul_eq_mul] using
        condExp_smul (μ := tdSamplingLaw M π T)
          (u z.1 * u z.2) (fun data ↦ ξ z.1 data * ξ z.2 data)
          (tdPastSigma T (k - 1))
    filter_upwards [hc, hpair z.1 z.2] with data hd hp
    rw [hd, hp]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with data hd hterms
  rw [hd]
  simp only [Finset.sum_apply]
  calc
    _ = ∑ z : State × State, (u z.1 * u z.2) * (if z.1 = z.2 then
        tdSquareFreshRowVariance M π η T V₀ k z.1 data else 0) :=
      Finset.sum_congr rfl (fun z hz ↦ hterms z)
    _ = _ := by simp [Fintype.sum_prod_type, pow_two]

/-- One-coordinate consequence of the finite-row square-variance and affine
update bounds, for predictable old iterates in `[0,H]`. -/
theorem tdSquareCenteredWeightedRow_condExp_sq_le_proxy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) (u : State → ℝ)
    (hu : ∀ s, 0 ≤ u s) (hMass : (∑ s, u s) ≤ 1) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      (tdSamplingLaw M π T)[(fun data ↦
        tdSquareCenteredWeightedRow M π η T V₀ k u data ^ 2) |
          tdPastSigma T (k - 1)] data ≤
        4 * M.effectiveHorizon ^ 2 * ∑ s, u s *
          (M.policyTransition π s).variance
            (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data) := by
  have hEq := tdSquareCenteredWeightedRow_condExp_sq_eq
    M π η T V₀ k hk hkT u
  have hCells : ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      tdSquareFreshRowVariance M π η T V₀ k s data ≤
        4 * M.effectiveHorizon ^ 2 *
          (M.policyTransition π s).variance
            (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data) := by
    apply ae_all_iff.mpr
    intro s
    have hEqCell := tdSquareCenteredConditionalSecondMoment_eq_rowVariance
      M π η T V₀ k hk hkT s
    have hLeCell := tdSquareCenteredConditionalSecondMoment_le_rowVariance
      M π η T V₀ h₀ hη k hk hkT s
    filter_upwards [hEqCell, hLeCell] with data he hle
    rw [← he]
    exact hle
  filter_upwards [hEq, hCells] with data hrow hcell
  have hMassOne (s : State) : u s ≤ 1 := by
    have hs := Finset.single_le_sum (s := Finset.univ) (f := u)
      (fun r hr ↦ hu r) (Finset.mem_univ s)
    linarith
  have hDiag : (∑ s, u s ^ 2 * tdSquareFreshRowVariance M π η T V₀ k s data) ≤
      ∑ s, u s * tdSquareFreshRowVariance M π η T V₀ k s data := by
    apply Finset.sum_le_sum
    intro s hs
    exact mul_le_mul_of_nonneg_right (by nlinarith [hu s, hMassOne s])
      ((M.policyTransition π s).variance_nonneg
        (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data ^ 2))
  calc
    _ = ∑ s, u s ^ 2 * tdSquareFreshRowVariance M π η T V₀ k s data := by
      rw [hrow]
    _ ≤ ∑ s, u s * tdSquareFreshRowVariance M π η T V₀ k s data := hDiag
    _ ≤ ∑ s, u s * (4 * M.effectiveHorizon ^ 2 *
        (M.policyTransition π s).variance
          (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hcell s) (hu s)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring

/-- The source fixed-terminal late-window row after update `k`: it is the
actual tail propagator row A_(k+1:t), with no extra γη_k factor. -/
noncomputable def tdSquareLateTerminalRow
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (q r : State) : ℝ :=
  tdPropagatorRow M π η k t q r

/-- The terminal-tail row has nonnegative coefficients and exact mass equal to
the contraction product over transitions after the source update. -/
theorem tdSquareLateTerminalRow_mass
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) (q : State)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    (∀ r, 0 ≤ tdSquareLateTerminalRow M π η t k q r) ∧
    (∑ r, tdSquareLateTerminalRow M π η t k q r) ≤ 1 := by
  constructor
  · intro r
    exact tdPropagatorRow_nonneg M π η k t hη q r
  · change (∑ r, tdPropagatorRow M π η k t q r) ≤ 1
    rw [tdPropagatorRow_sum M π η k t hkt q]
    apply Finset.prod_le_one
    · intro i hi
      have hii := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds M.discount η i M.discount_nonneg
        M.discount_lt_one.le (hη i (by omega) hii.2)).1
    · intro i hi
      have hii := Finset.mem_Icc.mp hi
      exact (tdRateContraction_bounds M.discount η i M.discount_nonneg
        M.discount_lt_one.le (hη i (by omega) hii.2)).2

/-! Fixed-terminal source-window conditional variance. The explicit late-window
premises preserve the exact `floor(t/2)+1≤k≤t` domain. -/
theorem tdSquareLateWindowIncrement_condExp_sq_le_sourceProxy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (htT : t ≤ T) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (n : ℕ) (hnFloor : t / 2 ≤ n) (hnT : n < t)
    (barη : ℝ) (hbar : η (n + 1) ≤ barη) (q : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      (tdSamplingLaw M π T)[
        (tdSquareLateWindowIncrement M π η T t V₀ q n ^ 2) |
          tdPastSigma T n] data ≤
        4 * M.effectiveHorizon ^ 2 * barη * (η (n + 1)) * M.discount ^ 2 *
          ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
            (M.policyTransition π r).variance
              (tdValueBefore M π η T n V₀ data) := by
  classical
  let k := n + 1
  let u := tdSquareLateTerminalRow M π η t k q
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkt : k ≤ t := by dsimp [k]; omega
  have hkT : k ≤ T := by dsimp [k]; omega
  have hWindow : t / 2 ≤ n ∧ n < t := ⟨hnFloor, hnT⟩
  have hWrap : tdSquareLateWindowIncrement M π η T t V₀ q n =
      tdSquareTerminalIncrement M π η T t V₀ q n := by
    simp [tdSquareLateWindowIncrement, hWindow]
  have htermRep : tdSquareTerminalIncrement M π η T t V₀ q n =
      fun data ↦ tdSquareCenteredWeightedRow M π η T V₀ k u data := by
    funext data
    simp only [tdSquareTerminalIncrement, if_pos hnT,
      tdSquareCenteredWeightedRow]
    dsimp [u, k, tdSquareLateTerminalRow]
    exact tdErrorPropagate_eq_row_sum M π η k t
      (fun r ↦ tdSquareCentered M π η T V₀ k r data) q
  have hRow : tdSquareLateWindowIncrement M π η T t V₀ q n =
      fun data ↦ tdSquareCenteredWeightedRow M π η T V₀ k u data :=
    hWrap.trans htermRep
  have hRowSq : (fun data ↦
      tdSquareLateWindowIncrement M π η T t V₀ q n data ^ 2) =ᵐ[tdSamplingLaw M π T]
      (fun data ↦ tdSquareCenteredWeightedRow M π η T V₀ k u data ^ 2) :=
    Filter.Eventually.of_forall fun data ↦ congrArg (fun z : ℝ ↦ z ^ 2)
      (congrFun hRow data)
  have hCondEq := condExp_congr_ae (m := tdPastSigma T n) hRowSq
  have huMass := tdSquareLateTerminalRow_mass M π η t k hk hkt q
    (fun i hi1 hi_t ↦ hη i hi1)
  have hηT : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi1 hiT
    exact hη i hi1
  have hRowBound := tdSquareCenteredWeightedRow_condExp_sq_le_proxy
    M π η T V₀ h₀ hηT k hk hkT u huMass.1 huMass.2
  have hηk := hη k hk
  have hbarη : 0 ≤ barη := le_trans hηk.1 hbar
  have hηSq : η k ^ 2 ≤ barη * η k := by
    have hmul := mul_le_mul_of_nonneg_right hbar hηk.1
    nlinarith [hmul]
  have hEtaGammaSq : (η k * M.discount) ^ 2 ≤
      barη * η k * M.discount ^ 2 := by
    calc
      (η k * M.discount) ^ 2 = η k ^ 2 * M.discount ^ 2 := by ring
      _ ≤ (barη * η k) * M.discount ^ 2 :=
        mul_le_mul_of_nonneg_right hηSq (sq_nonneg M.discount)
  have hVarOldNonneg (data : TDSamples State T) :
      0 ≤ ∑ r, u r * (M.policyTransition π r).variance
        (tdValueBefore M π η T n V₀ data) :=
    Finset.sum_nonneg fun r hr ↦ mul_nonneg (huMass.1 r)
      ((M.policyTransition π r).variance_nonneg
        (tdValueBefore M π η T n V₀ data))
  have hAffineSum (data : TDSamples State T) :
      (∑ r, u r * (M.policyTransition π r).variance
        (fun x ↦ tdSquareFreshUpdate M π η T V₀ k r x data)) =
      (η k * M.discount) ^ 2 *
        ∑ r, u r * (M.policyTransition π r).variance
          (tdValueBefore M π η T n V₀ data) := by
    calc
      _ = ∑ r, u r * ((η k * M.discount) ^ 2 *
          (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [tdSquareFreshUpdate_variance_eq_oldRow]
        simp [k]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have hRowBoundN : ∀ᵐ data ∂tdSamplingLaw M π T,
      (tdSamplingLaw M π T)[(fun data ↦
        tdSquareCenteredWeightedRow M π η T V₀ k u data ^ 2) | tdPastSigma T n] data ≤
        4 * M.effectiveHorizon ^ 2 * ∑ s, u s *
          (M.policyTransition π s).variance
            (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data) := by
    simpa [k] using hRowBound
  filter_upwards [hCondEq, hRowBoundN] with data hce hbound
  change (tdSamplingLaw M π T)[(fun data ↦
    tdSquareLateWindowIncrement M π η T t V₀ q n data ^ 2) | tdPastSigma T n] data ≤ _
    
  rw [hce]
  calc
    _ ≤ 4 * M.effectiveHorizon ^ 2 *
        ((η k * M.discount) ^ 2 *
          ∑ r, u r * (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data)) := by
      rw [hAffineSum] at hbound
      exact hbound
    _ ≤ 4 * M.effectiveHorizon ^ 2 *
        ((barη * η k * M.discount ^ 2) *
          ∑ r, u r * (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hEtaGammaSq (hVarOldNonneg data)
      · positivity
    _ = _ := by ring

end StatisticalRL.TemporalDifference
