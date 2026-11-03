import Formalization.ModelFree.TDTerminalCaps
import Formalization.ModelFree.TDStepSizeEarly

/-!

Early-update contribution to the actual TD predictable variance.
-/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Squared-row variance contribution restricted to the early source updates
`2k≤t`, reindexed by `k=n+1`. -/
noncomputable def tdEarlySquaredVarianceRows
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (s : State)
    (data : TDSamples State T) : ℝ :=
  ∑ n ∈ Finset.range t,
    if n < t / 2 then
      ∑ r, tdWeightedPropagatorRow M π η t (n + 1) s r ^ 2 *
        (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)
    else 0

/-- One early squared-row summand is bounded by the source rate weight squared.
This uses the actual weighted propagator row mass and the true-iterate
variance cap, pointwise in the realized sample array. -/
theorem tdEarlySquaredVarianceRow_le_rateSq
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t n : ℕ) (hn : n < t) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (s : State) (data : TDSamples State T) :
    (∑ r, tdWeightedPropagatorRow M π η t (n + 1) s r ^ 2 *
      (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)) ≤
      (M.discount ^ 2 * M.effectiveHorizon ^ 2) *
        tdRateWeight M.discount η t (n + 1) ^ 2 := by
  have hrow := td_squared_row_le_mass_sq
    (tdWeightedPropagatorRow M π η t (n + 1) s)
    (fun r ↦ (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data))
    (M.effectiveHorizon ^ 2)
    (tdWeightedPropagatorRow_nonneg M π η t (n + 1) (by omega) (by omega)
      hη s)
    (sq_nonneg _)
    (fun r ↦ tdValueBefore_variance_le_horizon_sq M π η T n V₀ h₀
      (fun i hi hin ↦ hη i hi (by omega)) data r)
  rw [tdWeightedPropagatorRow_sum M π η t (n + 1) (by omega) (by omega) s] at hrow
  change _ ≤ _
  nlinarith [hrow]

/-- The finite early index set has at most `T/2` elements, so a per-index
`C/T⁴` cap sums to `C/(2T³)`. The endpoint `t=0` is included. -/
theorem tdEarlyConstantSum_le
    (T t : ℕ) (hT : 0 < T) (ht : t ≤ T) (C : ℝ) (hC : 0 ≤ C) :
    (∑ n ∈ Finset.range t, if n < t / 2 then C / (T : ℝ) ^ 4 else 0) ≤
      C / (2 * (T : ℝ) ^ 3) := by
  classical
  have hf : (Finset.range t).filter (fun n ↦ n < t / 2) = Finset.range (t / 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hsum : (∑ n ∈ Finset.range t, if n < t / 2 then C / (T : ℝ) ^ 4 else 0) =
      (t / 2 : ℕ) * (C / (T : ℝ) ^ 4) := by
    rw [← Finset.sum_filter, hf]
    simp
  have hfloor : (t / 2 : ℕ) ≤ T / 2 := by omega
  have hfloorR : ((t / 2 : ℕ) : ℝ) ≤ (T : ℝ) / 2 := by
    have hn : 2 * (t / 2) ≤ T := by omega
    have hr : (2 : ℝ) * (t / 2 : ℕ) ≤ T := by exact_mod_cast hn
    linarith
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  rw [hsum]
  calc
    _ ≤ ((T : ℝ) / 2) * (C / (T : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right hfloorR (div_nonneg hC (pow_nonneg hTr.le 4))
    _ = _ := by field_simp [ne_of_gt hTr]

/-- Every early row contribution has the source `T⁻⁴` size under the exact
source early-weight premise. `2(n+1)≤t` is the same cutoff as `n<t/2` for
natural indices. -/
theorem tdEarlySquaredVarianceRows_le_budget_of_weight_bound
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (hT : 0 < T) (ht : t ≤ T)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hearly : ∀ k, 1 ≤ k → 2 * k ≤ t →
      tdRateWeight M.discount η t k ≤ 1 / (T : ℝ) ^ 2)
    (s : State) :
    ∀ data : TDSamples State T,
      tdEarlySquaredVarianceRows M π η T t V₀ s data ≤
        M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) := by
  intro data
  let C : ℝ := M.discount ^ 2 * M.effectiveHorizon ^ 2
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hstep (n : ℕ) (hn : n ∈ Finset.range t) :
      (if n < t / 2 then
        ∑ r, tdWeightedPropagatorRow M π η t (n + 1) s r ^ 2 *
          (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)
        else 0) ≤ if n < t / 2 then C / (T : ℝ)^4 else 0 := by
    have hnt : n < t := Finset.mem_range.mp hn
    by_cases hcut : n < t / 2
    · simp only [if_pos hcut]
      have hrate := hearly (n + 1) (by omega) (by omega)
      have hrate_nonneg := tdRateWeight_nonneg M.discount η t (n + 1)
        M.discount_nonneg M.discount_lt_one.le hη
      have hsquare := (sq_le_sq₀ hrate_nonneg
        (by positivity : 0 ≤ 1 / (T : ℝ)^2)).2 hrate
      have hrow := tdEarlySquaredVarianceRow_le_rateSq M π η T t n hnt V₀ h₀ hη s data
      calc
        _ ≤ C * tdRateWeight M.discount η t (n + 1) ^ 2 := by
          simpa [C] using hrow
        _ ≤ C * (1 / (T : ℝ)^2) ^ 2 := mul_le_mul_of_nonneg_left hsquare hC
        _ = C / (T : ℝ)^4 := by field_simp [ne_of_gt (show (0 : ℝ) < T by exact_mod_cast hT)]
    · simp only [if_neg hcut]
      exact le_rfl
  have hsum := Finset.sum_le_sum hstep
  change _ ≤ _
  calc
    _ ≤ ∑ n ∈ Finset.range t, if n < t / 2 then C / (T : ℝ)^4 else 0 := hsum
    _ ≤ C / (2 * (T : ℝ)^3) := tdEarlyConstantSum_le T t hT ht C hC
    _ = M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ)^3) := by rfl

/-- The source-corrected step-size hypotheses supply the early weight bound.
This wrapper records the exact large-T premise required by the standalone
`tdRateWeight_early_le_inv_sq` API and retains `t≤T` and source eligibility. -/
theorem tdEarlySquaredVarianceRows_le_budget_of_source_schedule
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T t : ℕ) (hT : 2 ≤ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hlarge : Real.log (T : ℝ)^2 ≤ c₁ * (1 - M.discount) * T)
    (hs : TDStepSizeSchedule M.discount c₁ c₂ T η)
    (ht : t ≤ T)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (s : State) :
    ∀ data : TDSamples State T,
      tdEarlySquaredVarianceRows M π η T t V₀ s data ≤
        M.discount ^ 2 * M.effectiveHorizon ^ 2 / (2 * (T : ℝ) ^ 3) := by
  have hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi hit
    exact td_schedule_rate_bounds M.discount c₁ c₂ T η hT M.discount_lt_one
      hc₁ hc₂ hs i hi (hit.trans ht)
  have hrate : ∀ k, 1 ≤ k → 2 * k ≤ t →
      tdRateWeight M.discount η t k ≤ 1 / (T : ℝ)^2 := by
    intro k hk hkt
    exact tdRateWeight_early_le_inv_sq M.discount c₁ c₂ T η hT
      M.discount_nonneg M.discount_lt_one hc₁ hc₂ hcprod hlarge hs t k ht htime hkt
  exact tdEarlySquaredVarianceRows_le_budget_of_weight_bound M π η T t
    (by omega) ht V₀ h₀ hη hrate s

end StatisticalRL.TemporalDifference
