import Formalization.ModelFree.QLearningLateRateSchedule
import Formalization.ModelFree.QLearningOptimalFluctuationHistory

/-! source-schedule late weights and deterministic caps. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qScheduleCapStateMeasurable : MeasurableSpace State := ⊤
local instance qScheduleCapActionMeasurable : MeasurableSpace Action := ⊤

/-- Source's η̄, retaining its exact factor two and min with one. -/
noncomputable def qSourceLateCap (γ c₂ : ℝ) (T : ℕ) : ℝ :=
  min 1 (2 * Real.log (T : ℝ)^3 / (c₂ * (1-γ) * (T : ℝ)))

/-- The actual finite schedule yields the source late squared-weight cap. -/
theorem qSourceLate_weight_squares_le (γ c₁ c₂ : ℝ) (T u : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ1 : γ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hu : u ≤ T) (hs : qSourceRateSchedule γ c₁ c₂ T η) :
    (∑ i ∈ Finset.Icc (T/2+1) u, (qPositiveWeight η u i)^2) ≤ qSourceLateCap γ c₂ T := by
  have hcap : 0 ≤ qSourceLateCap γ c₂ T := by
    unfold qSourceLateCap
    have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
    have hgap : 0 < 1-γ := by linarith
    positivity
  apply qLate_weight_squares_le η T u _ hcap
  · intro k hk hku
    exact qSourceRate_unit_interval γ c₁ c₂ T η hT hγ1 hc₁ hc₂ hs k (le_trans hku hu)
  · intro k hk hku
    exact qSourceRate_late_le γ c₁ c₂ T η hT hγ1 hc₂ hs k hk (le_trans hku hu)

/-- Source-schedule global increment bound, including all inactive t≥T. -/
theorem qSourceOptimalIncrement_abs_le (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (c₁ c₂ : ℝ) (T u : ℕ) (hT : 2 ≤ T) (hu : u ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (s : State) (a : Action) (t : ℕ) (data : QSamples State Action T) :
    |qOptimalFluctuationIncrement M η T u s a t data| ≤
      M.discount * qSourceLateCap M.discount c₂ T * M.effectiveHorizon := by
  classical
  have hcap : 0 ≤ qSourceLateCap M.discount c₂ T := by
    unfold qSourceLateCap
    have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
    have hgap : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
    positivity
  by_cases h : t < T ∧ T/2 < t+1 ∧ t+1 ≤ u
  · have hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1 := by
      intro k hk hku
      exact qSourceRate_unit_interval M.discount c₁ c₂ T η hT M.discount_lt_one hc₁ hc₂ hs k (le_trans hku hu)
    have hw := qPositiveWeight_late_le η T u (t+1) h.2.1 h.2.2 hη
      (qSourceLateCap M.discount c₂ T) (fun k hk hku ↦
        qSourceRate_late_le M.discount c₁ c₂ T η hT M.discount_lt_one hc₂ hs k hk (le_trans hku hu))
    have hb := qOptimalFluctuation_abs_le M η T u t s a h hη data
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw.2 M.discount_nonneg) M.effectiveHorizon_nonneg)
  · have hz := congrFun (qOptimalFluctuation_inactive M η T u t s a h) data
    simp only [Pi.zero_apply, hz, abs_zero]
    exact mul_nonneg (mul_nonneg M.discount_nonneg hcap) M.effectiveHorizon_nonneg

/- Fixed-row predictable variance and Freedman are established in subsequent modules; uniform row and time bounds remain separate. -/
end StatisticalRL.QLearning
