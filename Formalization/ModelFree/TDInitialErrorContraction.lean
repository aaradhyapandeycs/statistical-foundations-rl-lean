import Formalization.ModelFree.TDActualErrorUnroll
import Formalization.ModelFree.TDErrorCaps
import Formalization.ModelFree.TDStepSizeBudget

/-! Deterministic initial-error contraction for the finite TD schedule. The result
uses the actual chronological propagator, the source-budget consequence, and
the `k = 0` initial-rate weight; it does not constrain or use `η₀`. -/
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Under the printed source budget, the initial error in the exact TD error
unrolling is at most `H/T²` at every source-eligible terminal. The proof uses
the actual chronological propagator and the `k=0` initial rate weight; η₀ is
not constrained or used. -/
theorem tdInitialError_contraction_of_source_budget
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (c₁ c₂ c₃ ε δ : ℝ)
    (hT : 2 ≤ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hconstants : 1 ≤ c₁ * c₃ * Real.log 2 ^ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεmax : ε ≤ M.effectiveHorizon)
    (hs : TDStepSizeSchedule M.discount c₁ c₂ T η)
    (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ))
    (ht : t ≤ T)
    (helig : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) :
    ‖tdErrorPropagate M π η 0 t (V₀ - M.trajectoryExpectedValue π)‖ ≤
      M.effectiveHorizon / (T : ℝ) ^ 2 := by
  letI : Nonempty State := M.state_nonempty
  have hcard : 0 < Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hS : 1 ≤ Fintype.card State := by omega
  have hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 := by
    intro i hi hit
    exact td_schedule_rate_bounds M.discount c₁ c₂ T η hT M.discount_lt_one
      hc₁ hc₂ hs i hi (hit.trans ht)
  have hweightCaps := tdRateWeight_step_size_of_mainBudget M.discount c₁ c₂ c₃
    δ ε (Fintype.card State) T η hS hT M.discount_nonneg M.discount_lt_one
    hc₁ hc₂ hc₃ hcprod hconstants hδ hδ1 hε hεmax hs hBudget t 0 ht
    (by omega : 0 ≤ t) helig
  have hweight := hweightCaps.1 (by omega : 2 * 0 ≤ t)
  have hprod : (∏ i ∈ Finset.Icc 1 t, tdRateContraction M.discount η i) ≤
      1 / (T : ℝ) ^ 2 := by
    simpa only [tdRateWeight_initial] using hweight
  have hprod_nonneg : 0 ≤ ∏ i ∈ Finset.Icc 1 t, tdRateContraction M.discount η i := by
    have hn := tdRateWeight_nonneg M.discount η t 0 M.discount_nonneg
      M.discount_lt_one.le hη
    simpa only [tdRateWeight_initial] using hn
  have hres : ‖V₀ - M.trajectoryExpectedValue π‖ ≤ M.effectiveHorizon := by
    apply (pi_norm_le_iff_of_nonneg M.effectiveHorizon_nonneg).2
    intro s
    have h0s := h₀ s
    have hπ := M.trajectoryExpectedValue_bounds π s
    change |V₀ s - M.trajectoryExpectedValue π s| ≤ M.effectiveHorizon
    rw [abs_le]
    constructor <;> dsimp [DiscountedMDP.effectiveHorizon] at * <;> linarith
  have hprop := tdErrorPropagate_norm_le M π η 0 t (by omega) hη
    (V₀ - M.trajectoryExpectedValue π)
  have hmul := mul_le_mul hprod hres (norm_nonneg _) (by positivity :
    (0 : ℝ) ≤ 1 / (T : ℝ) ^ 2)
  calc
    _ ≤ (∏ i ∈ Finset.Icc 1 t, tdRateContraction M.discount η i) *
        ‖V₀ - M.trajectoryExpectedValue π‖ := hprop
    _ ≤ (1 / (T : ℝ) ^ 2) * M.effectiveHorizon := hmul
    _ = M.effectiveHorizon / (T : ℝ) ^ 2 := by ring

end StatisticalRL.TemporalDifference
