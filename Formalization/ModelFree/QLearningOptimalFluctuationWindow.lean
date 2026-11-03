import Formalization.ModelFree.QLearningOptimalFluctuationHistory

/-! Source-only draft: inactive layers, fixed-terminal indexing and individual late weights. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptWindowStateMeasurable : MeasurableSpace State := ⊤
local instance qOptWindowActionMeasurable : MeasurableSpace Action := ⊤

/-- Inactive layers are exactly zero, including every layer beyond T. -/
theorem qOptimalFluctuation_inactive (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action)
    (h : ¬ (t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u)) :
    qOptimalFluctuationIncrement M η T u s a t = 0 := by
  funext data
  simp [qOptimalFluctuationIncrement, h]

/-- Source positive-update weight is bounded by its own learning rate. -/
theorem qPositiveWeight_le_rate (η : ℕ → ℝ) (u i : ℕ) (hi : 1 ≤ i) (hiu : i ≤ u)
    (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1) :
    qPositiveWeight η u i ≤ η i := by
  unfold qPositiveWeight
  have hp : (∏ j ∈ Finset.Icc (i+1) u, (1 - η j)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact sub_nonneg.mpr (hη j (by omega) hj'.2).2
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      linarith [(hη j (by omega) hj'.2).1]
  calc
    η i * _ ≤ η i * 1 := mul_le_mul_of_nonneg_left hp (hη i hi hiu).1
    _ = η i := mul_one _

/-- Late source weights inherit an explicit source rate cap; no probability event
or conclusion-shaped sample cap is assumed. -/
theorem qPositiveWeight_late_le (η : ℕ → ℝ) (T u i : ℕ) (hi : T/2 < i)
    (hiu : i ≤ u) (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1)
    (cap : ℝ) (hcap : ∀ k, T/2 < k → k ≤ u → η k ≤ cap) :
    0 ≤ qPositiveWeight η u i ∧ qPositiveWeight η u i ≤ cap := by
  have hi1 : 1 ≤ i := by omega
  exact ⟨qPositiveWeight_nonneg η u i hi1 hiu hη,
    (qPositiveWeight_le_rate η u i hi1 hiu hη).trans (hcap i hi hiu)⟩

/-- Source-indexed form of ξ_u: i starts strictly after floor(T/2); the
transition sample is the genuine zero-based coordinate i−1. -/
noncomputable def qSourceIndexedFluctuation (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T u : ℕ) (hu : u ≤ T) (s : State) (a : Action)
    (data : QSamples State Action T) : ℝ :=
  ∑ i : {i // i ∈ Finset.Icc (T/2+1) u},
    M.discount * qPositiveWeight η u i.1 *
      (qTrueOptimalValue M (data ((s,a), ⟨i.1-1, by
        have hi := Finset.mem_Icc.mp i.2
        omega⟩)) - (M.transition s a).expectation (qTrueOptimalValue M))

/- The source-indexed expression uses a finite subtype to retain the membership
proof needed for the valid sample coordinate. Prove its
sum equals qOptimalFluctuation for u≤T by a bijection t↦t+1 between active
indices in range T and Icc (floor(T/2)+1) u. Do not assert the stronger source
sum-of-squared-weights bound until deriving ∑η_i^(u)≤1 by telescoping; then
0≤w_i≤cap implies ∑w_i²≤cap*∑w_i≤cap. Empty windows and T=0 need explicit
handling. No Freedman bound is established. -/
end StatisticalRL.QLearning
