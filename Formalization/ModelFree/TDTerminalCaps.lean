import Formalization.ModelFree.TDTerminalHistory
import Formalization.ModelFree.TDErrorCaps
import Formalization.ModelFree.TDWeightMass

/-! Conservative actual fixed-terminal TD caps. A is an explicit deterministic
weight envelope; connecting it to the corrected source schedule is separate.
The actual caps are derived from the exact squared-row conditional identity. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdTerminalCapsStateMeasurable : MeasurableSpace State := ⊤

/-- Bounded actual iterates give a true-row variance cap, without independence. -/
theorem tdValueBefore_variance_le_horizon_sq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T n : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ η i ∧ η i ≤ 1)
    (data : TDSamples State T) (s : State) :
    (M.policyTransition π s).variance (tdValueBefore M π η T n V₀ data) ≤ M.effectiveHorizon ^ 2 := by
  apply (M.policyTransition π s).variance_le_expectation_sq _ |>.trans
  calc
    _ ≤ (M.policyTransition π s).expectation (fun _ ↦ M.effectiveHorizon ^ 2) := by
      apply FiniteDistribution.expectation_mono
      intro r
      have hv := tdIterate_bounds_positive_rates M π η (tdSamplesExtend M T data) V₀ h₀ n hη r
      change tdIterate M π η (tdSamplesExtend M T data) V₀ n r ^ 2 ≤ _
      nlinarith [M.effectiveHorizon_nonneg]
    _ = _ := (M.policyTransition π s).expectation_const _

/-- A bounded variance vector and nonnegative actual row yield its mass-square cap. -/
theorem td_squared_row_le_mass_sq (u v : State → ℝ) (C : ℝ)
    (hu : ∀ s, 0 ≤ u s) (hC : 0 ≤ C) (hv : ∀ s, v s ≤ C) :
    (∑ s, u s ^ 2 * v s) ≤ C * (∑ s, u s) ^ 2 := by
  have hm := td_nonnegative_row_variance_proxy u (fun _ ↦ (1 : ℝ)) hu (by simp)
  simp only [mul_one] at hm
  calc
    _ ≤ ∑ s, u s ^ 2 * C := Finset.sum_le_sum fun s hs ↦
      mul_le_mul_of_nonneg_left (hv s) (sq_nonneg _)
    _ = C * (∑ s, u s ^ 2) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ C * (∑ s, u s) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hm]) hC

/-- Range/source-update reindexing, including terminal zero. -/
theorem td_sum_range_succ_eq_Icc (f : ℕ → ℝ) (t : ℕ) :
    (∑ n ∈ Finset.range t, f (n + 1)) = ∑ k ∈ Finset.Icc 1 t, f k := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), ih]

/-- The actual raw-prefix predictable second moment has a conservative cap.
All cross-state cancellation is supplied by the proved exact squared-row identity. -/
theorem tdTerminalVarianceSum_le_weight_cap (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (s : State) (A : ℝ) (hA : 0 ≤ A)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hcap : ∀ k, 1 ≤ k → k ≤ t → tdRateWeight M.discount η t k ≤ A) :
    ∀ᵐ data ∂tdSamplingLaw M π T,
      tdTerminalVarianceSum M π η T t V₀ s data ≤ M.discount ^ 2 * M.effectiveHorizon ^ 3 * A := by
  filter_upwards [tdTerminalVarianceSum_eq_squaredRows M π η T t ht V₀ s] with data hd
  rw [hd]
  have hw := tdRateWeight_sq_sum_le M.discount η t A M.discount_nonneg M.discount_lt_one hA hη hcap
  have hterm (n : ℕ) (hn : n ∈ Finset.range t) :
      (∑ r, tdWeightedPropagatorRow M π η t (n+1) s r ^ 2 *
        (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data)) ≤
      (M.discount ^ 2 * M.effectiveHorizon ^ 2) * tdRateWeight M.discount η t (n+1) ^ 2 := by
    have hnlt := Finset.mem_range.mp hn
    have hh := td_squared_row_le_mass_sq (tdWeightedPropagatorRow M π η t (n+1) s)
      (fun r ↦ (M.policyTransition π r).variance (tdValueBefore M π η T n V₀ data))
      (M.effectiveHorizon ^ 2)
      (tdWeightedPropagatorRow_nonneg M π η t (n+1) (by omega) (by omega) hη s)
      (sq_nonneg _) (fun r ↦ tdValueBefore_variance_le_horizon_sq M π η T n V₀ h₀
        (fun i hi hin ↦ hη i hi (by omega)) data r)
    rw [tdWeightedPropagatorRow_sum M π η t (n+1) (by omega) (by omega) s] at hh
    nlinarith [hh]
  calc
    _ ≤ ∑ n ∈ Finset.range t, (M.discount ^ 2 * M.effectiveHorizon ^ 2) *
        tdRateWeight M.discount η t (n+1) ^ 2 := Finset.sum_le_sum hterm
    _ = (M.discount ^ 2 * M.effectiveHorizon ^ 2) *
        ∑ k ∈ Finset.Icc 1 t, tdRateWeight M.discount η t k ^ 2 := by
      rw [← Finset.mul_sum, td_sum_range_succ_eq_Icc (fun k ↦ tdRateWeight M.discount η t k ^ 2) t]
    _ ≤ (M.discount ^ 2 * M.effectiveHorizon ^ 2) * (A / (1 - M.discount)) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by unfold DiscountedMDP.effectiveHorizon; ring

/-- Global padded increment cap for the same actual sequence and fixed terminal. -/
theorem tdTerminalIncrement_abs_le_weight_cap (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ)
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (s : State) (A : ℝ) (hA : 0 ≤ A)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hcap : ∀ k, 1 ≤ k → k ≤ t → tdRateWeight M.discount η t k ≤ A)
    (n : ℕ) (data : TDSamples State T) :
    |tdTerminalIncrement M π η T t V₀ s n data| ≤ 2 * M.discount * M.effectiveHorizon * A := by
  by_cases hn : n < t
  · have hh := tdWeightedErrorIncrement_norm_le_horizon M π η (tdSamplesExtend M T data) V₀ h₀
      t (n+1) (by omega) (by omega) hη
    have hc := norm_le_pi_norm (tdWeightedErrorIncrement M π η (tdSamplesExtend M T data) V₀ t (n+1)) s
    change |tdWeightedErrorIncrement M π η (tdSamplesExtend M T data) V₀ t (n+1) s| ≤ _
    have hu := mul_le_mul_of_nonneg_left (hcap (n+1) (by omega) (by omega))
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) M.discount_nonneg) M.effectiveHorizon_nonneg)
    rw [Real.norm_eq_abs] at hc
    nlinarith
  · rw [tdTerminalIncrement_zero_after M π η T t V₀ s n (by omega)]
    simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) M.discount_nonneg)
      M.effectiveHorizon_nonneg) hA

end StatisticalRL.TemporalDifference
