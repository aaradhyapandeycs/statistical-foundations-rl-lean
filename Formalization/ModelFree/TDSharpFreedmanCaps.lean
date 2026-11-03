import Formalization.ModelFree.TDSharpVarianceSum
import Formalization.ModelFree.TDTerminalCaps

/-! Derived increment and coarse variance caps for fixed-terminal late-window TD; concentration remains separate. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpFreedmanCapsStateMeasurable : MeasurableSpace State := ⊤

/-- The actual fresh update ranges in an interval of width `ηγH`: its old
state contribution is fixed and only the true policy-row draw varies. -/
theorem tdSquareFreshUpdate_pair_diff_abs_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) (s x y : State)
    (data : TDSamples State T) :
    |tdSquareFreshUpdate M π η T V₀ k s x data -
      tdSquareFreshUpdate M π η T V₀ k s y data| ≤
        η k * M.discount * M.effectiveHorizon := by
  let v := tdValueBefore M π η T (k - 1) V₀ data
  have hv (r : State) : 0 ≤ v r ∧ v r ≤ M.effectiveHorizon := by
    exact tdIterate_bounds_of_positive_rates M π η
      (tdSamplesExtend M T data) V₀ h₀ (k - 1)
      (fun i hi1 hiT ↦ hη i hi1 (by omega)) r
  have he := hη k hk hkT
  change |((1 - η k) * v s + η k * (policyReward M π s + M.discount * v x)) -
      ((1 - η k) * v s + η k * (policyReward M π s + M.discount * v y))| ≤ _
  rw [show ((1 - η k) * v s + η k * (policyReward M π s + M.discount * v x)) -
      ((1 - η k) * v s + η k * (policyReward M π s + M.discount * v y)) =
        η k * M.discount * (v x - v y) by ring]
  rw [abs_mul, abs_of_nonneg (mul_nonneg he.1 M.discount_nonneg)]
  have hxy : |v x - v y| ≤ M.effectiveHorizon := by
    rw [abs_le]
    constructor <;> linarith [(hv x).1, (hv x).2, (hv y).1, (hv y).2]
  exact mul_le_mul_of_nonneg_left hxy (mul_nonneg he.1 M.discount_nonneg)

/-- Fresh-square differences are bounded by twice the horizon times the
fresh-update interval width. -/
theorem tdSquareFreshUpdate_sq_pair_diff_abs_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) (s x y : State)
    (data : TDSamples State T) :
    |tdSquareFreshUpdate M π η T V₀ k s x data ^ 2 -
      tdSquareFreshUpdate M π η T V₀ k s y data ^ 2| ≤
        2 * η k * M.discount * M.effectiveHorizon ^ 2 := by
  have hxy := tdSquareFreshUpdate_pair_diff_abs_le M π η T V₀ h₀ hη k hk hkT s x y data
  have he := hη k hk hkT
  have hu (z : State) :
      0 ≤ tdSquareFreshUpdate M π η T V₀ k s z data ∧
        tdSquareFreshUpdate M π η T V₀ k s z data ≤ M.effectiveHorizon := by
    have hv := tdIterate_bounds_of_positive_rates M π η
      (tdSamplesExtend M T data) V₀ h₀ (k - 1)
      (fun i hi1 hiT ↦ hη i hi1 (by omega))
    have hs : 0 ≤ tdValueBefore M π η T (k - 1) V₀ data s ∧
        tdValueBefore M π η T (k - 1) V₀ data s ≤ M.effectiveHorizon := by
      simpa [tdValueBefore] using hv s
    have hz : 0 ≤ tdValueBefore M π η T (k - 1) V₀ data z ∧
        tdValueBefore M π η T (k - 1) V₀ data z ≤ M.effectiveHorizon := by
      simpa [tdValueBefore] using hv z
    have hr := policyReward_bounds M π s
    have htarget :
        0 ≤ policyReward M π s + M.discount * tdValueBefore M π η T (k - 1) V₀ data z ∧
        policyReward M π s + M.discount * tdValueBefore M π η T (k - 1) V₀ data z ≤
          M.effectiveHorizon := by
      constructor
      · exact add_nonneg hr.1 (mul_nonneg M.discount_nonneg hz.1)
      · calc
          _ ≤ 1 + M.discount * M.effectiveHorizon :=
            add_le_add hr.2 (mul_le_mul_of_nonneg_left hz.2 M.discount_nonneg)
          _ = M.effectiveHorizon := M.effectiveHorizon_recursion
    change 0 ≤ (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s +
        η k * (policyReward M π s + M.discount * tdValueBefore M π η T (k - 1) V₀ data z) ∧ _
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr he.2) hs.1)
        (mul_nonneg he.1 htarget.1)
    · change (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s +
        η k * (policyReward M π s + M.discount *
          tdValueBefore M π η T (k - 1) V₀ data z) ≤ M.effectiveHorizon
      nlinarith [mul_nonneg (sub_nonneg.mpr he.2)
          (sub_nonneg.mpr hs.2),
        mul_nonneg he.1 (sub_nonneg.mpr htarget.2)]
  rw [show tdSquareFreshUpdate M π η T V₀ k s x data ^ 2 -
      tdSquareFreshUpdate M π η T V₀ k s y data ^ 2 =
        (tdSquareFreshUpdate M π η T V₀ k s x data -
          tdSquareFreshUpdate M π η T V₀ k s y data) *
        (tdSquareFreshUpdate M π η T V₀ k s x data +
          tdSquareFreshUpdate M π η T V₀ k s y data) by ring]
  rw [abs_mul]
  have hsum : |tdSquareFreshUpdate M π η T V₀ k s x data +
      tdSquareFreshUpdate M π η T V₀ k s y data| ≤ 2 * M.effectiveHorizon := by
    rw [abs_of_nonneg (add_nonneg (hu x).1 (hu y).1)]
    linarith [ (hu x).2, (hu y).2 ]
  have hprod := mul_le_mul hxy hsum
    (abs_nonneg _)
    (mul_nonneg (mul_nonneg he.1 M.discount_nonneg) M.effectiveHorizon_nonneg)
  calc
    _ ≤ (η k * M.discount * M.effectiveHorizon) * (2 * M.effectiveHorizon) := hprod
    _ = 2 * η k * M.discount * M.effectiveHorizon ^ 2 := by ring

/-- The centered square differs from its actual true-row conditional mean by
at most the range width, almost surely under the actual finite sample law. -/
theorem tdSquareCentered_abs_le_late_rate
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) (s : State) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      |tdSquareCentered M π η T V₀ k s data| ≤
        2 * η k * M.discount * M.effectiveHorizon ^ 2 := by
  let p := M.policyTransition π s
  let u := fun x data ↦ tdSquareFreshUpdate M π η T V₀ k s x data ^ 2
  let mean := tdSquareFreshRowMean M π η T V₀ k s
  have hmean :
      (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s |
        tdPastSigma T (k - 1)] =ᵐ[tdSamplingLaw M π T] mean := by
    have hobs := tdSquareObservation_eq_freshSquare M π η T V₀ k hk hkT s
    have hobsAE : tdSquareObservation M π η T V₀ k s =ᵐ[tdSamplingLaw M π T]
        fun data ↦ u (data (s,⟨k,by omega⟩)) data :=
      Filter.Eventually.of_forall fun data ↦ congrFun hobs data
    have hfresh := tdFresh_predictable_square_condExp M π T (k - 1) (by omega) s
      (fun x data ↦ tdSquareFreshUpdate M π η T V₀ k s x data)
      (by
        intro x
        dsimp [tdSquareFreshUpdate]
        exact (stronglyMeasurable_const.mul
          (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ s)).add
          (stronglyMeasurable_const.mul
            (stronglyMeasurable_const.add
              (stronglyMeasurable_const.mul
                (tdValueBefore_stronglyMeasurable M π η T (k - 1) (by omega) V₀ x)))) )
    have h := condExp_congr_ae (m := tdPastSigma T (k - 1)) hobsAE
    exact h.trans (by simpa [mean, tdSquareFreshRowMean, u, Nat.sub_add_cancel hk] using hfresh)
  have hpoint (data : TDSamples State T) (x : State) :
      |u x data - p.expectation (fun y ↦ u y data)| ≤
        2 * η k * M.discount * M.effectiveHorizon ^ 2 := by
    have hp := tdSquareFreshUpdate_sq_pair_diff_abs_le M π η T V₀ h₀ hη k hk hkT s
    have hD : 0 ≤ 2 * η k * M.discount * M.effectiveHorizon ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hη k hk hkT).1)
        M.discount_nonneg) (sq_nonneg _)
    have hlo : u x data - (2 * η k * M.discount * M.effectiveHorizon ^ 2) ≤
        p.expectation (fun y ↦ u y data) := by
      calc
        _ = p.expectation (fun _ ↦ u x data -
            (2 * η k * M.discount * M.effectiveHorizon ^ 2)) := by
              simp [FiniteDistribution.expectation_const]
        _ ≤ p.expectation (fun y ↦ u y data) := p.expectation_mono fun y ↦ by
              have h := hp x y data
              rw [abs_le] at h
              linarith [h.1]
    have hhi : p.expectation (fun y ↦ u y data) ≤
        u x data + 2 * η k * M.discount * M.effectiveHorizon ^ 2 := by
      calc
        _ ≤ p.expectation (fun _ ↦ u x data +
            (2 * η k * M.discount * M.effectiveHorizon ^ 2)) := p.expectation_mono fun y ↦ by
              have h := hp x y data
              rw [abs_le] at h
              linarith [h.2]
        _ = _ := by simp [FiniteDistribution.expectation_const]
    rw [abs_le]
    constructor <;> linarith
  filter_upwards [hmean] with data hm
  have hcenter := by
    change tdSquareCentered M π η T V₀ k s data =
      tdSquareObservation M π η T V₀ k s data -
        (tdSamplingLaw M π T)[tdSquareObservation M π η T V₀ k s |
          tdPastSigma T (k - 1)] data
    rfl
  rw [hcenter, hm]
  have hobs := tdSquareObservation_eq_freshSquare M π η T V₀ k hk hkT s
  simpa [mean, tdSquareFreshRowMean, hobs] using hpoint data (data (s,⟨k,by omega⟩))

/-- Deterministic cap on each actual zero-padded late-window martingale
increment. The early and post-terminal slots vanish exactly. -/
theorem tdSquareLateWindowIncrement_abs_le
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hbar0 : 0 ≤ barη)
    (hbar : ∀ k, t / 2 + 1 ≤ k → k ≤ t → η k ≤ barη)
    (q : State) (n : ℕ) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      |tdSquareLateWindowIncrement M π η T t V₀ q n data| ≤
        2 * barη * M.effectiveHorizon ^ 2 := by
  by_cases hn : t / 2 ≤ n ∧ n < t
  · have hk : 1 ≤ n + 1 := by omega
    have hkT : n + 1 ≤ T := by omega
    have hfloor : t / 2 + 1 ≤ n + 1 := by omega
    have hterminal : n + 1 ≤ t := by omega
    have hηT : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 :=
      fun i hi1 hit ↦ hη i hi1 (by omega)
    have hc := tdSquareCentered_abs_le_late_rate M π η T V₀ h₀
      (fun i hi1 hiT ↦ hη i hi1 hiT) (n + 1) hk hkT
    have htail : ∀ r, 0 ≤ tdPropagatorRow M π η (n + 1) t q r :=
      fun r ↦ tdPropagatorRow_nonneg M π η (n + 1) t hηT q r
    have hmass : (∑ r, tdPropagatorRow M π η (n + 1) t q r) ≤ 1 := by
      rw [tdPropagatorRow_sum M π η (n + 1) t (by omega) q]
      apply Finset.prod_le_one
      · intro i hi
        have hii := Finset.mem_Icc.mp hi
        have hi1 : 1 ≤ i := by omega
        exact (tdRateContraction_bounds M.discount η i M.discount_nonneg
          M.discount_lt_one.le (hηT i hi1 hii.2)).1
      · intro i hi
        have hii := Finset.mem_Icc.mp hi
        have hi1 : 1 ≤ i := by omega
        exact (tdRateContraction_bounds M.discount η i M.discount_nonneg
          M.discount_lt_one.le (hηT i hi1 hii.2)).2
    have hcenters : ∀ᵐ data ∂tdSamplingLaw M π T, ∀ r,
        |tdSquareCentered M π η T V₀ (n + 1) r data| ≤
          2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2 :=
      ae_all_iff.mpr fun r ↦ tdSquareCentered_abs_le_late_rate M π η T V₀ h₀
        (fun i hi1 hiT ↦ hη i hi1 hiT) (n + 1) hk hkT r
    have hηb := hbar (n + 1) hfloor hterminal
    filter_upwards [hcenters] with data hdata
    have hrow := tdErrorPropagate_eq_row_sum M π η (n + 1) t
      (fun r ↦ tdSquareCentered M π η T V₀ (n + 1) r data) q
    rw [tdSquareLateWindowIncrement, if_pos hn]
    change |tdSquareTerminalIncrement M π η T t V₀ q n data| ≤ _
    rw [tdSquareTerminalIncrement, if_pos hn.2]
    rw [hrow]
    have hsum : |∑ r, tdPropagatorRow M π η (n + 1) t q r *
        tdSquareCentered M π η T V₀ (n + 1) r data| ≤
        ∑ r, tdPropagatorRow M π η (n + 1) t q r *
          (2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2) := by
      calc
        _ ≤ ∑ r, |tdPropagatorRow M π η (n + 1) t q r *
            tdSquareCentered M π η T V₀ (n + 1) r data| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          rw [abs_mul, abs_of_nonneg (htail r)]
          exact mul_le_mul_of_nonneg_left (hdata r) (htail r)
    have hcoef : 2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2 ≤
        2 * barη * M.effectiveHorizon ^ 2 := by
      have hrate : η (n + 1) * M.discount ≤ barη := by
        calc
          _ ≤ barη * M.discount :=
            mul_le_mul_of_nonneg_right hηb M.discount_nonneg
          _ ≤ barη := by
            nlinarith [mul_nonneg hbar0 (sub_nonneg.mpr M.discount_lt_one.le)]
      calc
        2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2 =
            (η (n + 1) * M.discount) * (2 * M.effectiveHorizon ^ 2) := by ring
        _ ≤ barη * (2 * M.effectiveHorizon ^ 2) :=
          mul_le_mul_of_nonneg_right hrate
            (mul_nonneg (by norm_num) (sq_nonneg M.effectiveHorizon))
        _ = 2 * barη * M.effectiveHorizon ^ 2 := by ring
    have hcoefnn : 0 ≤ 2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hη (n + 1) (by omega) hkT).1)
        M.discount_nonneg) (sq_nonneg M.effectiveHorizon)
    calc
      _ ≤ ∑ r, tdPropagatorRow M π η (n + 1) t q r *
          (2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2) := hsum
      _ = (2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2) *
          ∑ r, tdPropagatorRow M π η (n + 1) t q r := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ (2 * η (n + 1) * M.discount * M.effectiveHorizon ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hmass hcoefnn
      _ ≤ 2 * barη * M.effectiveHorizon ^ 2 := by
        have hηb := hbar (n + 1) hfloor hterminal
        nlinarith [M.discount_lt_one.le]
  · have hzero : tdSquareLateWindowIncrement M π η T t V₀ q n = fun _ ↦ 0 := by
      funext data
      simp [tdSquareLateWindowIncrement, hn]
    filter_upwards [] with data
    rw [congrFun hzero data]
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hbar0)
      (sq_nonneg M.effectiveHorizon)

/-- Pointwise coarse cap on the random late-window proxy. It uses only the
actual iterate range, true-row variance bound, nonnegative tail rows and the
proved rate-weight mass identity; it does not use the sharp energy bound. -/
theorem tdSquareLateWindowRandomProxy_le_coarse
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hbar0 : 0 ≤ barη)
    (q : State) (data : TDSamples State T) :
    tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
      barη * M.effectiveHorizon ^ 3 := by
  have hterm (n : ℕ) (hn : n ∈ Finset.range t) :
      (if t / 2 ≤ n then
        barη * η (n + 1) * M.discount ^ 2 *
          ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
            (M.policyTransition π r).variance
              (tdValueBefore M π η T n V₀ data)
       else 0) ≤
        barη * M.discount * M.effectiveHorizon ^ 2 *
          tdRateWeight M.discount η t (n + 1) := by
    have hnlt := Finset.mem_range.mp hn
    by_cases hlate : t / 2 ≤ n
    · have hk : 1 ≤ n + 1 := by omega
      have hkt : n + 1 ≤ t := by omega
      have hηt : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 :=
        fun i hi1 hit ↦ hη i hi1
      have hmass := tdSquareLateTerminalRow_mass M π η t (n + 1) hk hkt q hηt
      have hvar (r : State) :
          (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data) ≤ M.effectiveHorizon ^ 2 := by
        exact tdValueBefore_variance_le_horizon_sq M π η T n V₀ h₀
          (fun i hi1 hi_n ↦ hη i hi1) data r
      have hrows : 0 ≤ ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
          (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data) ∧
          ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
          (M.policyTransition π r).variance
            (tdValueBefore M π η T n V₀ data) ≤
              M.effectiveHorizon ^ 2 *
                ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r := by
        constructor
        · apply Finset.sum_nonneg
          intro r hr
          exact mul_nonneg (hmass.1 r)
            ((M.policyTransition π r).variance_nonneg _)
        · calc
            _ ≤ ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
                M.effectiveHorizon ^ 2 := Finset.sum_le_sum fun r hr ↦
                  mul_le_mul_of_nonneg_left (hvar r) (hmass.1 r)
            _ = M.effectiveHorizon ^ 2 *
                ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro r hr
                  ring
      have hweight :
          tdRateWeight M.discount η t (n + 1) = η (n + 1) *
            (∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r) := by
        change tdRateWeight M.discount η t (n + 1) = η (n + 1) *
          (∑ r, tdPropagatorRow M π η (n + 1) t q r)
        rw [tdRateWeight, if_pos hkt, if_neg (by omega : n + 1 ≠ 0)]
        rw [tdPropagatorRow_sum M π η (n + 1) t hkt q]
      rw [if_pos hlate]
      have hcoef : 0 ≤ barη * η (n + 1) * M.discount ^ 2 :=
        mul_nonneg (mul_nonneg hbar0 (hη (n + 1) (by omega)).1) (sq_nonneg _)
      calc
        _ = (barη * η (n + 1) * M.discount ^ 2) *
            (∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
              (M.policyTransition π r).variance
                (tdValueBefore M π η T n V₀ data)) := by ring
        _ ≤ (barη * η (n + 1) * M.discount ^ 2) *
            (M.effectiveHorizon ^ 2 *
              ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r) :=
          mul_le_mul_of_nonneg_left hrows.2 hcoef
        _ = barη * η (n + 1) * M.discount ^ 2 *
            M.effectiveHorizon ^ 2 *
            ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r := by ring
        _ ≤ barη * M.discount * M.effectiveHorizon ^ 2 *
            tdRateWeight M.discount η t (n + 1) := by
          rw [hweight]
          have hγsq : M.discount ^ 2 ≤ M.discount := by
            nlinarith [M.discount_nonneg, M.discount_lt_one.le]
          have hnonneg : 0 ≤ barη * η (n + 1) * M.effectiveHorizon ^ 2 *
              ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r :=
            mul_nonneg
              (mul_nonneg (mul_nonneg hbar0 (hη (n + 1) (by omega)).1)
                (sq_nonneg M.effectiveHorizon))
              (Finset.sum_nonneg fun r hr ↦ hmass.1 r)
          nlinarith
    · simp only [if_neg hlate]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hbar0 M.discount_nonneg)
          (sq_nonneg M.effectiveHorizon))
        (tdRateWeight_nonneg M.discount η t (n + 1)
          M.discount_nonneg M.discount_lt_one.le
          (fun i hi1 hiT ↦ hη i hi1))
  have hsum := Finset.sum_le_sum hterm
  unfold tdSquareLateWindowRandomProxy
  calc
    _ ≤ ∑ n ∈ Finset.range t,
        barη * M.discount * M.effectiveHorizon ^ 2 *
          tdRateWeight M.discount η t (n + 1) := hsum
    _ = barη * M.discount * M.effectiveHorizon ^ 2 *
        ∑ k ∈ Finset.Icc 1 t, tdRateWeight M.discount η t k := by
      rw [← Finset.mul_sum, td_sum_range_succ_eq_Icc]
    _ ≤ barη * M.discount * M.effectiveHorizon ^ 2 *
        (1 / (1 - M.discount)) := by
      have hcoef : 0 ≤ barη * M.discount * M.effectiveHorizon ^ 2 :=
        mul_nonneg (mul_nonneg hbar0 M.discount_nonneg)
          (sq_nonneg M.effectiveHorizon)
      apply mul_le_mul_of_nonneg_left
        (tdRateWeight_sum_le_horizon M.discount η t M.discount_nonneg
          M.discount_lt_one (fun i hi1 hi_t ↦ hη i hi1))
        hcoef
    _ = barη * M.discount * M.effectiveHorizon ^ 3 := by
      rw [DiscountedMDP.effectiveHorizon]
      ring
    _ ≤ barη * M.effectiveHorizon ^ 3 := by
      calc
        _ = barη * (M.discount * M.effectiveHorizon ^ 3) := by ring
        _ ≤ barη * (1 * M.effectiveHorizon ^ 3) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right M.discount_lt_one.le
              (pow_nonneg M.effectiveHorizon_nonneg 3)) hbar0
        _ = _ := by ring

end StatisticalRL.TemporalDifference
