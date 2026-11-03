import Formalization.ModelFree.TDSharpEnergy
import Formalization.ModelFree.TDWeightMass
import Formalization.ModelFree.TDSharpVarianceSum

/-! Actual late-window TD energy and random-proxy inequality; concentration remains separate. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpEnergyProxyStateMeasurable : MeasurableSpace State := ⊤

/-- Actual squared iterate used as the potential in source `eq:TD-square-energy`.-/
noncomputable def tdSharpSquarePotential
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (j : ℕ)
    (data : TDSamples State T) : State → ℝ :=
  fun s ↦ tdValueBefore M π η T j V₀ data s ^ 2

/-- Exact source innovation: actual squared iterate minus its conditional
expectation given the strict used prefix before source update `k`. -/
noncomputable def tdSharpSquareInnovation
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ)
    (data : TDSamples State T) : State → ℝ :=
  fun s ↦ tdSquareCentered M π η T V₀ k s data

/-- Source active sample indices. `n=k−1`, so this is exactly
`floor(t/2)+1≤k≤t`. -/
def tdSharpEnergyWindow (t : ℕ) : Finset ℕ :=
  Finset.Icc (t / 2 + 1) t

/-- Row positivity comes from the actual stochastic transition and source rate
bounds, not an assumed positive matrix. -/
theorem tdSharpEnergyProxy_tailRow_nonneg
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (q r : State) :
    0 ≤ tdPropagatorRow M π η k t q r :=
  tdPropagatorRow_nonneg M π η k t hη q r

/-- The actual chronological tail row has mass at most one. The product in the
identity is over updates `k+1,...,t`, so no `η_k γ` multiplier is folded into
the tail row. -/
theorem tdSharpEnergyProxy_tailRow_mass
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t k : ℕ) (hkt : k ≤ t) (q : State)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1) :
    (∑ r, tdPropagatorRow M π η k t q r) ≤ 1 := by
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

/-- Actual iterate range used to bound the squared potential by `H²`. -/
theorem tdSharpSquarePotential_range
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (j : ℕ) (hj : j ≤ T) (data : TDSamples State T) :
    ∀ s, 0 ≤ tdSharpSquarePotential M π η T V₀ j data s ∧
      tdSharpSquarePotential M π η T V₀ j data s ≤ M.effectiveHorizon ^ 2 := by
  intro s
  have hv := tdIterate_bounds_of_positive_rates M π η
    (tdSamplesExtend M T data) V₀ h₀ j
    (fun i hi1 hij ↦ hη i hi1) s
  have hv' : 0 ≤ tdValueBefore M π η T j V₀ data s ∧
      tdValueBefore M π η T j V₀ data s ≤ M.effectiveHorizon := by
    simpa [tdValueBefore] using hv
  change 0 ≤ tdValueBefore M π η T j V₀ data s ^ 2 ∧
    tdValueBefore M π η T j V₀ data s ^ 2 ≤ M.effectiveHorizon ^ 2
  exact ⟨sq_nonneg _, (sq_le_sq₀ hv'.1 M.effectiveHorizon_nonneg).2 hv'.2⟩

/-- The compiled arbitrary-sequence telescope instantiated at the actual
squared iterates. -/
theorem tdSharpSquarePotential_telescope
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (V₀ : State → ℝ) (data : TDSamples State T) :
    (∑ k ∈ tdSharpEnergyWindow t,
      tdErrorPropagate M π η k t
        (tdErrorTransition M π η k
          (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
          tdSharpSquarePotential M π η T V₀ k data)) =
      tdErrorPropagate M π η (t / 2) t
        (tdSharpSquarePotential M π η T V₀ (t / 2) data) -
        tdSharpSquarePotential M π η T V₀ t data := by
  exact tdWeightedSquareEnergy_telescope M π η (t / 2) t (by omega)
    (fun j ↦ tdSharpSquarePotential M π η T V₀ j data)

/-- Endpoint of the actual potential telescope is at most `H²` coordinatewise.
This uses the real propagator contraction, not a supplied norm bound. -/
theorem tdSharpSquarePotential_endpoint_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (data : TDSamples State T) :
    ∀ q, tdErrorPropagate M π η (t / 2) t
        (tdSharpSquarePotential M π η T V₀ (t / 2) data) q -
        tdSharpSquarePotential M π η T V₀ t data q ≤ M.effectiveHorizon ^ 2 := by
  intro q
  have hRange (j : ℕ) (hj : j ≤ T) (s : State) :
      0 ≤ tdSharpSquarePotential M π η T V₀ j data s ∧
        tdSharpSquarePotential M π η T V₀ j data s ≤ M.effectiveHorizon ^ 2 := by
    have hv := tdIterate_bounds_of_positive_rates M π η
      (tdSamplesExtend M T data) V₀ h₀ j
      (fun i hi1 hij ↦ hη i hi1 (by omega)) s
    have hv' : 0 ≤ tdValueBefore M π η T j V₀ data s ∧
        tdValueBefore M π η T j V₀ data s ≤ M.effectiveHorizon := by
      simpa [tdValueBefore] using hv
    change 0 ≤ tdValueBefore M π η T j V₀ data s ^ 2 ∧
      tdValueBefore M π η T j V₀ data s ^ 2 ≤ M.effectiveHorizon ^ 2
    exact ⟨sq_nonneg _, (sq_le_sq₀ hv'.1 M.effectiveHorizon_nonneg).2 hv'.2⟩
  have hF : ∀ s, 0 ≤ tdSharpSquarePotential M π η T V₀ (t / 2) data s ∧
      tdSharpSquarePotential M π η T V₀ (t / 2) data s ≤ M.effectiveHorizon ^ 2 := by
    intro s
    exact hRange (t / 2) (by omega) s
  have hprop := tdErrorPropagate_le_const_of_interval M π η (t / 2) t
    (by omega) (fun i hi1 hiT ↦ hη i hi1 (by omega))
    (tdSharpSquarePotential M π η T V₀ (t / 2) data)
    (M.effectiveHorizon ^ 2) (sq_nonneg _ ) hF
  have htRange : ∀ s, 0 ≤ tdSharpSquarePotential M π η T V₀ t data s := by
    intro s
    exact (hRange t ht s).1
  have htail := (hprop q).2
  have hterminal := htRange q
  linarith

/-- The deterministic remainder is a sub-sum of the exact source learning-rate
weights. This declaration keeps the actual terminal tail and late window. -/
theorem tdSharpEnergyProxy_remainder_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (t : ℕ) (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (q : State) :
    2 * M.effectiveHorizon *
      ∑ k ∈ tdSharpEnergyWindow t,
        η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q ≤
      2 * M.effectiveHorizon ^ 2 := by
  have hweight (k : ℕ) (hk : k ∈ tdSharpEnergyWindow t) :
      η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q =
        tdRateWeight M.discount η t k := by
    have hi := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := by dsimp [tdSharpEnergyWindow] at hk; omega
    have hkt : k ≤ t := hi.2
    have hconst := congrFun (tdErrorPropagate_const M π η k t hkt 1) q
    unfold tdRateWeight
    rw [if_pos hkt, if_neg (by omega : k ≠ 0)]
    simp only [mul_one] at hconst
    rw [hconst]
  have hsub : tdSharpEnergyWindow t ⊆ Finset.Icc 1 t := by
    intro k hk
    have hi := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by dsimp [tdSharpEnergyWindow] at hk; omega, hi.2⟩
  have hsumSub :
      (∑ k ∈ tdSharpEnergyWindow t, tdRateWeight M.discount η t k) ≤
        ∑ k ∈ Finset.Icc 1 t, tdRateWeight M.discount η t k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k hk hk' ↦ tdRateWeight_nonneg M.discount η t k
        M.discount_nonneg M.discount_lt_one.le hη)
  have hsumMass := tdRateWeight_sum_le_horizon M.discount η t
    M.discount_nonneg M.discount_lt_one hη
  calc
    _ = 2 * M.effectiveHorizon *
        ∑ k ∈ tdSharpEnergyWindow t, tdRateWeight M.discount η t k := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact hweight k hk
    _ ≤ 2 * M.effectiveHorizon *
        ∑ k ∈ Finset.Icc 1 t, tdRateWeight M.discount η t k :=
      mul_le_mul_of_nonneg_left hsumSub
        (mul_nonneg (by norm_num) M.effectiveHorizon_nonneg)
    _ ≤ 2 * M.effectiveHorizon * (1 / (1 - M.discount)) :=
      mul_le_mul_of_nonneg_left hsumMass
        (mul_nonneg (by norm_num) M.effectiveHorizon_nonneg)
    _ = 2 * M.effectiveHorizon ^ 2 := by
      rw [DiscountedMDP.effectiveHorizon]
      ring

/-- Source energy/proxy inequality. The proof body explicitly builds the common actual
energy event, compares coefficients, propagates by the actual tail, and
assembles the source late-window sum and telescope. -/
theorem tdSquareLateWindowRandomProxy_le_energy
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hbar0 : 0 ≤ barη) (hbarHalf : barη ≤ 1 / 2)
    (hbar : ∀ k, t / 2 + 1 ≤ k → k ≤ t → η k ≤ barη)
    (q : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
        (barη / (1 - barη)) *
          (3 * M.effectiveHorizon ^ 2 +
            tdSquareLateWindowSum M π η T t V₀ q data) := by
  /- Source assembly: intersect the `tdSquaredIterateEnergy`
  events for `k∈Icc (t/2+1) t` and all states; rewrite the conditional-energy
  right side as `A_k F_{k−1}−F_k+C_k+2η_kH`; compare coefficients using
  `η_k≤barη≤1/2`; propagate each coordinate inequality with
  `tdErrorPropagate_mono`; sum and split by linearity. The `A_kF_{k−1}−F_k`
  terms are exactly the compiled telescope. Bound its endpoint with
  `tdSharpSquarePotential_endpoint_le`, the constant-vector remainder with
  `tdSharpEnergyProxy_remainder_le`, and identify the centered sum with the
  late-window source sum. This theorem has no desired-result premise. -/
  have henergyAt (k : ℕ) : ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      k ∈ tdSharpEnergyWindow t →
        η k * (1 - η k) * M.discount ^ 2 *
            (M.policyTransition π s).variance
              (tdValueBefore M π η T (k - 1) V₀ data) ≤
          (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s ^ 2 +
            η k * M.discount *
              (M.policyTransition π s).expectation
                (fun x ↦ tdValueBefore M π η T (k - 1) V₀ data x ^ 2) -
            (tdSamplingLaw M π T)[(fun data ↦
              tdValueBefore M π η T k V₀ data s ^ 2) |
                tdPastSigma T (k - 1)] data +
            2 * η k * M.effectiveHorizon := by
    by_cases hk : k ∈ tdSharpEnergyWindow t
    · have hi := Finset.mem_Icc.mp hk
      have hstep := tdSquaredIterateEnergy M π η T V₀ h₀
        (fun i hi1 _ ↦ hη i hi1) k (by omega) (by omega)
      filter_upwards [hstep] with data hdata
      intro s _
      have hH : 2 * η k / (1 - M.discount) =
          2 * η k * M.effectiveHorizon := by
        rw [DiscountedMDP.effectiveHorizon]
        ring
      rw [hH] at hdata
      exact hdata s
    · filter_upwards [] with data
      intro s hs
      exact (hk hs).elim
  have hcommon := ae_all_iff.mpr henergyAt
  filter_upwards [hcommon] with data hdata
  have henergy : ∀ k ∈ tdSharpEnergyWindow t, ∀ s,
      η k * (1 - η k) * M.discount ^ 2 *
          (M.policyTransition π s).variance
            (tdValueBefore M π η T (k - 1) V₀ data) ≤
        (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s ^ 2 +
          η k * M.discount *
            (M.policyTransition π s).expectation
              (fun x ↦ tdValueBefore M π η T (k - 1) V₀ data x ^ 2) -
          (tdSamplingLaw M π T)[(fun data ↦
            tdValueBefore M π η T k V₀ data s ^ 2) |
              tdPastSigma T (k - 1)] data +
          2 * η k * M.effectiveHorizon := by
    intro k hk s
    exact hdata k s hk
  let c : ℝ := barη / (1 - barη)
  have hden : 0 < 1 - barη := by linarith
  have hc : 0 ≤ c := div_nonneg hbar0 hden.le
  have hcoef (k : ℕ) (hk : k ∈ tdSharpEnergyWindow t) :
      barη ≤ c * (1 - η k) := by
    have hi := Finset.mem_Icc.mp hk
    have hηk := hη k (by omega)
    have hηbar : η k ≤ barη := hbar k (by omega) hi.2
    have hmul := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hηbar 1) hbar0
    dsimp [c]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hden).2 hmul
  have hstate (k : ℕ) (hk : k ∈ tdSharpEnergyWindow t) (s : State) :
      barη * η k * M.discount ^ 2 *
          (M.policyTransition π s).variance
            (tdValueBefore M π η T (k - 1) V₀ data) ≤
        c * (tdErrorTransition M π η k
              (tdSharpSquarePotential M π η T V₀ (k - 1) data) s -
            tdSharpSquarePotential M π η T V₀ k data s +
            tdSquareCentered M π η T V₀ k s data +
            2 * η k * M.effectiveHorizon) := by
    have hi := Finset.mem_Icc.mp hk
    have hηk := hη k (by omega)
    have hvar := (M.policyTransition π s).variance_nonneg
      (tdValueBefore M π η T (k - 1) V₀ data)
    have hfactor := hcoef k hk
    have hscale : barη * η k * M.discount ^ 2 *
          (M.policyTransition π s).variance
            (tdValueBefore M π η T (k - 1) V₀ data) ≤
        c * (η k * (1 - η k) * M.discount ^ 2 *
          (M.policyTransition π s).variance
            (tdValueBefore M π η T (k - 1) V₀ data)) := by
      have hx : 0 ≤ η k * M.discount ^ 2 *
          (M.policyTransition π s).variance
            (tdValueBefore M π η T (k - 1) V₀ data) :=
        mul_nonneg (mul_nonneg hηk.1 (sq_nonneg _)) hvar
      have hmul := mul_le_mul_of_nonneg_right hfactor hx
      nlinarith [hmul]
    have hsrc := henergy k hk s
    have hrhs :
        (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s ^ 2 +
          η k * M.discount *
            (M.policyTransition π s).expectation
              (fun x ↦ tdValueBefore M π η T (k - 1) V₀ data x ^ 2) -
          (tdSamplingLaw M π T)[(fun data ↦
            tdValueBefore M π η T k V₀ data s ^ 2) |
              tdPastSigma T (k - 1)] data +
          2 * η k * M.effectiveHorizon =
        tdErrorTransition M π η k
            (tdSharpSquarePotential M π η T V₀ (k - 1) data) s -
          tdSharpSquarePotential M π η T V₀ k data s +
          tdSquareCentered M π η T V₀ k s data +
          2 * η k * M.effectiveHorizon := by
      rw [show tdSharpSquarePotential M π η T V₀ (k - 1) data =
          (fun x ↦ tdValueBefore M π η T (k - 1) V₀ data x ^ 2) by rfl,
        show tdSharpSquarePotential M π η T V₀ k data =
          (fun x ↦ tdValueBefore M π η T k V₀ data x ^ 2) by rfl]
      simp [tdErrorTransition, tdSharpSquarePotential, tdSquareCentered,
        tdSquareObservation, tdSquareConditionalMean]
      rw [show (fun data : TDSamples State T ↦
          tdValueBefore M π η T k V₀ data s ^ 2) =
          tdSquareObservation M π η T V₀ k s by
            funext data
            rfl]
    rw [hrhs] at hsrc
    calc
      _ ≤ c * (η k * (1 - η k) * M.discount ^ 2 *
          (M.policyTransition π s).variance
            (tdValueBefore M π η T (k - 1) V₀ data)) := hscale
      _ ≤ _ := mul_le_mul_of_nonneg_left hsrc hc
  have htailRates : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 :=
    fun i hi1 _ ↦ hη i hi1
  have htail (k : ℕ) (hk : k ∈ tdSharpEnergyWindow t) :
      barη * η k * M.discount ^ 2 *
          tdErrorPropagate M π η k t
            (fun s ↦ (M.policyTransition π s).variance
              (tdValueBefore M π η T (k - 1) V₀ data)) q ≤
        c * tdErrorPropagate M π η k t
          (tdErrorTransition M π η k
              (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
            tdSharpSquarePotential M π η T V₀ k data +
            (fun s ↦ tdSquareCentered M π η T V₀ k s data) +
            (fun _ ↦ 2 * η k * M.effectiveHorizon)) q := by
    have hmono := tdErrorPropagate_mono M π η k t htailRates
      (fun s ↦ barη * η k * M.discount ^ 2 *
        (M.policyTransition π s).variance
          (tdValueBefore M π η T (k - 1) V₀ data))
      (fun s ↦ c * (tdErrorTransition M π η k
          (tdSharpSquarePotential M π η T V₀ (k - 1) data) s -
        tdSharpSquarePotential M π η T V₀ k data s +
        tdSquareCentered M π η T V₀ k s data +
        2 * η k * M.effectiveHorizon))
      (fun s ↦ hstate k hk s) q
    simpa only [tdErrorPropagate_mul, Pi.mul_apply] using hmono
  have hsumTail :
      (∑ k ∈ tdSharpEnergyWindow t,
        barη * η k * M.discount ^ 2 *
          tdErrorPropagate M π η k t
            (fun s ↦ (M.policyTransition π s).variance
              (tdValueBefore M π η T (k - 1) V₀ data)) q) ≤
        ∑ k ∈ tdSharpEnergyWindow t,
          c * tdErrorPropagate M π η k t
            (tdErrorTransition M π η k
                (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
              tdSharpSquarePotential M π η T V₀ k data +
              (fun s ↦ tdSquareCentered M π η T V₀ k s data) +
              (fun _ ↦ 2 * η k * M.effectiveHorizon)) q := by
    apply Finset.sum_le_sum
    intro k hk
    exact htail k hk
  have hproxyIndex :
      tdSquareLateWindowRandomProxy M π η T t V₀ barη q data =
        ∑ k ∈ tdSharpEnergyWindow t,
          barη * η k * M.discount ^ 2 *
            tdErrorPropagate M π η k t
              (fun s ↦ (M.policyTransition π s).variance
                (tdValueBefore M π η T (k - 1) V₀ data)) q := by
    classical
    unfold tdSquareLateWindowRandomProxy
    have hfilter :
        (∑ n ∈ Finset.range t,
          if t / 2 ≤ n then
            barη * η (n + 1) * M.discount ^ 2 *
              ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
                (M.policyTransition π r).variance
                  (tdValueBefore M π η T n V₀ data)
          else 0) =
        ∑ n ∈ tdSquareLateWindowIndices t,
          barη * η (n + 1) * M.discount ^ 2 *
            ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
              (M.policyTransition π r).variance
                (tdValueBefore M π η T n V₀ data) := by
      rw [← Finset.sum_filter]
      rfl
    rw [hfilter]
    unfold tdSharpEnergyWindow
    apply Finset.sum_bij (fun n _ ↦ n + 1)
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hrange := Finset.mem_range.mp hn'.1
      exact Finset.mem_Icc.mpr (by omega)
    · intro n₁ hn₁ n₂ hn₂ heq
      omega
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      refine ⟨k - 1, ?_, by omega⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · omega
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hnlt := Finset.mem_range.mp hn'.1
      have hrow := tdErrorPropagate_eq_row_sum M π η (n + 1) t
        (fun r ↦ (M.policyTransition π r).variance
          (tdValueBefore M π η T n V₀ data)) q
      rw [show n + 1 - 1 = n by omega]
      simp only [tdSquareLateTerminalRow]
      rw [← hrow]
  have hlinear (k : ℕ) :
      tdErrorPropagate M π η k t
          (tdErrorTransition M π η k
              (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
            tdSharpSquarePotential M π η T V₀ k data +
            (fun s ↦ tdSquareCentered M π η T V₀ k s data) +
            (fun _ ↦ 2 * η k * M.effectiveHorizon)) q =
        tdErrorPropagate M π η k t
            (tdErrorTransition M π η k
                (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
              tdSharpSquarePotential M π η T V₀ k data) q +
          tdErrorPropagate M π η k t
            ((fun s ↦ tdSquareCentered M π η T V₀ k s data)) q +
          tdErrorPropagate M π η k t
            (fun _ ↦ 2 * η k * M.effectiveHorizon) q := by
    simp only [tdErrorPropagate_add, Pi.add_apply]
  have hconstant (k : ℕ) (hk : k ∈ tdSharpEnergyWindow t) :
      tdErrorPropagate M π η k t
          (fun _ ↦ 2 * η k * M.effectiveHorizon) q =
        2 * M.effectiveHorizon * (η k *
          tdErrorPropagate M π η k t (fun _ ↦ 1) q) := by
    have hi := Finset.mem_Icc.mp hk
    rw [tdErrorPropagate_const M π η k t hi.2,
      tdErrorPropagate_const M π η k t hi.2]
    simp only [mul_one]
    ring
  have hsumR :
      (∑ k ∈ tdSharpEnergyWindow t,
        tdErrorPropagate M π η k t
          (tdErrorTransition M π η k
              (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
            tdSharpSquarePotential M π η T V₀ k data +
            (fun s ↦ tdSquareCentered M π η T V₀ k s data) +
            (fun _ ↦ 2 * η k * M.effectiveHorizon)) q) =
        tdErrorPropagate M π η (t / 2) t
            (tdSharpSquarePotential M π η T V₀ (t / 2) data) q -
          tdSharpSquarePotential M π η T V₀ t data q +
          tdSquareLateWindowSum M π η T t V₀ q data +
          2 * M.effectiveHorizon *
            ∑ k ∈ tdSharpEnergyWindow t,
              η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q := by
    calc
      _ = (∑ k ∈ tdSharpEnergyWindow t,
            tdErrorPropagate M π η k t
              (tdErrorTransition M π η k
                  (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
                tdSharpSquarePotential M π η T V₀ k data) q) +
          (∑ k ∈ tdSharpEnergyWindow t,
            tdErrorPropagate M π η k t
              ((fun s ↦ tdSquareCentered M π η T V₀ k s data)) q) +
          ∑ k ∈ tdSharpEnergyWindow t,
            tdErrorPropagate M π η k t
              (fun _ ↦ 2 * η k * M.effectiveHorizon) q := by
        simp_rw [hlinear]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (tdErrorPropagate M π η (t / 2) t
            (tdSharpSquarePotential M π η T V₀ (t / 2) data) q -
          tdSharpSquarePotential M π η T V₀ t data q) +
          tdSquareLateWindowSum M π η T t V₀ q data +
          2 * M.effectiveHorizon *
            ∑ k ∈ tdSharpEnergyWindow t,
              η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q := by
        have htelescope := tdSharpSquarePotential_telescope M π η T t ht
          (fun i hi1 hiT ↦ hη i hi1) V₀ data
        have htelescope_q :
            (∑ k ∈ tdSharpEnergyWindow t,
              tdErrorPropagate M π η k t
                (tdErrorTransition M π η k
                    (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
                  tdSharpSquarePotential M π η T V₀ k data) q) =
              tdErrorPropagate M π η (t / 2) t
                (tdSharpSquarePotential M π η T V₀ (t / 2) data) q -
              tdSharpSquarePotential M π η T V₀ t data q := by
          simpa only [Finset.sum_apply] using congrFun htelescope q
        have hsource :
            (∑ k ∈ tdSharpEnergyWindow t,
              tdErrorPropagate M π η k t
                ((fun s ↦ tdSquareCentered M π η T V₀ k s data)) q) =
              tdSquareLateWindowSum M π η T t V₀ q data := by
          rw [tdSquareLateWindowSum_eq_source]
          rfl
        have hconstsum :
            (∑ k ∈ tdSharpEnergyWindow t,
              tdErrorPropagate M π η k t
                (fun _ ↦ 2 * η k * M.effectiveHorizon) q) =
              2 * M.effectiveHorizon *
                ∑ k ∈ tdSharpEnergyWindow t,
                  η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q := by
          calc
            _ = ∑ k ∈ tdSharpEnergyWindow t,
                  2 * M.effectiveHorizon *
                    (η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hconstant k hk
            _ = _ := by rw [Finset.mul_sum]
        rw [htelescope_q, hsource, hconstsum]
  have hendpoint := tdSharpSquarePotential_endpoint_le M π η T t ht
    (fun i hi1 hiT ↦ hη i hi1) V₀ h₀ data q
  have hrem := tdSharpEnergyProxy_remainder_le M π η t
    (fun i hi1 hiT ↦ hη i hi1) q
  have hproxyBound :
      tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
        ∑ k ∈ tdSharpEnergyWindow t,
          c * tdErrorPropagate M π η k t
            (tdErrorTransition M π η k
                (tdSharpSquarePotential M π η T V₀ (k - 1) data) -
              tdSharpSquarePotential M π η T V₀ k data +
              (fun s ↦ tdSquareCentered M π η T V₀ k s data) +
              (fun _ ↦ 2 * η k * M.effectiveHorizon)) q := by
    rw [hproxyIndex]
    exact hsumTail
  rw [← Finset.mul_sum] at hproxyBound
  rw [hsumR] at hproxyBound
  have hconstbound :
      2 * M.effectiveHorizon *
          ∑ k ∈ tdSharpEnergyWindow t,
            η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q ≤
        2 * M.effectiveHorizon ^ 2 := hrem
  have hcombined :
      tdErrorPropagate M π η (t / 2) t
            (tdSharpSquarePotential M π η T V₀ (t / 2) data) q -
          tdSharpSquarePotential M π η T V₀ t data q +
        2 * M.effectiveHorizon *
          ∑ k ∈ tdSharpEnergyWindow t,
            η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q ≤
        3 * M.effectiveHorizon ^ 2 := by
    linarith [hendpoint, hconstbound]
  have hscaled := mul_le_mul_of_nonneg_left hcombined hc
  have hfinal : c * (
      (tdErrorPropagate M π η (t / 2) t
          (tdSharpSquarePotential M π η T V₀ (t / 2) data) q -
        tdSharpSquarePotential M π η T V₀ t data q) +
      tdSquareLateWindowSum M π η T t V₀ q data +
      2 * M.effectiveHorizon *
        ∑ k ∈ tdSharpEnergyWindow t,
          η k * tdErrorPropagate M π η k t (fun _ ↦ 1) q) ≤
    c * (3 * M.effectiveHorizon ^ 2 +
      tdSquareLateWindowSum M π η T t V₀ q data) := by
    nlinarith [hscaled]
  have hresult := hproxyBound.trans hfinal
  simpa [c] using hresult

end StatisticalRL.TemporalDifference
