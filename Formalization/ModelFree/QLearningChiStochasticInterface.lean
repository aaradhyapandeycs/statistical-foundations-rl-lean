import Formalization.ModelFree.QLearningChiResidualUpper
import Formalization.ModelFree.QLearningOptimalFreedman

/-! Interface for deterministic robust comparator fluctuations.
Deterministic event inclusion is proved. Probability of the radius
event remains an explicit unproved development obligation, not a premise of a
purported unconditional concentration theorem. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiStochasticStateMeasurable : MeasurableSpace State := ⊤
local instance qChiStochasticActionMeasurable : MeasurableSpace Action := ⊤

/-- Fixed terminal u, deterministic value v, and actual fresh source draw n+1.
The state-action sample coordinate is indexed by n, with exact late padding. -/
noncomputable def qChiFixedValueIncrement (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u : ℕ) (v : State → ℝ) (s : State) (a : Action) (n : ℕ)
    (data : QSamples State Action T) : ℝ :=
  if hn : n < T ∧ T / 2 < n+1 ∧ n+1 ≤ u then
    M.discount * qPositiveWeight η u (n+1) *
      (v (data ((s,a), ⟨n,hn.1⟩)) - (M.transition s a).expectation v)
  else 0

noncomputable def qChiComparatorFluctuation (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u : ℕ) (Q : State → Action → ℝ) (s : State) (a : Action)
    (data : QSamples State Action T) : ℝ :=
  ∑ n ∈ Finset.range T, qChiFixedValueIncrement M η T u (qLearningValue M Q) s a n data

/-- Both signs on one event. At source confidence delta this combined event
should have probability >=1-delta, using delta/2 for each sign. -/
noncomputable def qChiComparatorRadiusEvent (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) : Set (QSamples State Action T) :=
  {data | ∀ (s : State) (a : Action) (j : Fin T), T/2 < j.val+1 →
    let Qp := qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
    let Qm := qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
    (|qChiComparatorFluctuation M η T (j.val+1) Qp s a data| ≤
      M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Qp)) +
        (M.discount / 6) * ρ * M.effectiveHorizon) ∧
    (|qChiComparatorFluctuation M η T (j.val+1) Qm s a data| ≤
      M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Qm)) +
        (M.discount / 6) * ρ * M.effectiveHorizon)}

noncomputable def qChiComparatorAbsorptionEvent (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) : Set (QSamples State Action T) :=
  {data | ∀ (s : State) (a : Action) (j : Fin T), T/2 < j.val+1 →
    let Qp := qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
    let Qm := qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
    |qChiComparatorFluctuation M η T (j.val+1) Qp s a data| ≤ qComparatorResidualPlus M Qp s a ∧
    |qChiComparatorFluctuation M η T (j.val+1) Qm s a data| ≤ qComparatorResidualMinus M Qm s a}

/-- Pointwise variance-radius absorption, with no stochastic independence or
probability premise. The missing concentration theorem concerns the left set. -/
theorem qChi_radiusEvent_subset_absorptionEvent (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    qChiComparatorRadiusEvent M η T ρ hρ ⊆ qChiComparatorAbsorptionEvent M η T ρ hρ := by
  intro data hd s a j hj
  have hh := hd s a j hj
  have hb := qChi_actualComparatorResidual_absorbs_radius M ρ hρ s a
  exact ⟨hh.1.trans hb.1, hh.2.trans hb.2⟩

end StatisticalRL.QLearning
