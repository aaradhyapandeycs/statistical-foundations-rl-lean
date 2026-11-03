import Formalization.ModelFree.QLearningChiFixedValueMoments
import Formalization.Probability.FreedmanNaturalHistory

/-! Genuine next-prefix adaptation and natural-history
transfer for deterministic fixed-value fluctuations, retaining exact padding. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiHistoryStateMeasurable : MeasurableSpace State := ⊤
local instance qChiHistoryActionMeasurable : MeasurableSpace Action := ⊤

/-- Fixed-terminal source increment factors through the prefix after layer t. -/
theorem qChiFixedFluctuation_factors_nextPast (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) (data : QSamples State Action T) :
    qChiFixedFluctuationIncrement M v η T u s a t data =
      qChiFixedFluctuationIncrement M v η T u s a t
        (qCompletePast M T (t+1) (qPastData T (t+1) data)) := by
  classical
  by_cases ht : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u
  · have hmem : ((s,a), (⟨t,ht.1⟩ : Fin T)) ∈
        qPastIndices (State := State) (Action := Action) T (t+1) := by simp [qPastIndices]
    simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, ht, qCompletePast, qPastData, hmem]
  · simp [qChiFixedFluctuationIncrement, qChiFixedValueIncrement, ht]

/-- Every increment is measurable once its own layer has been observed. -/
theorem qChiFixedFluctuation_strong_nextPast (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    StronglyMeasurable[qPastSigma T (t+1)] (qChiFixedFluctuationIncrement M v η T u s a t) := by
  let F := fun code ↦ qChiFixedFluctuationIncrement M v η T u s a t (qCompletePast M T (t+1) code)
  have hm : Measurable F := measurable_of_countable _
  have hp : Measurable[qPastSigma T (t+1)] (qPastData (State := State) (Action := Action) T (t+1)) :=
    comap_measurable _
  have heq : F ∘ qPastData T (t+1) = qChiFixedFluctuationIncrement M v η T u s a t := by
    funext data
    exact (qChiFixedFluctuation_factors_nextPast M v η T u t s a data).symm
  rw [← heq]
  exact (hm.comp hp).stronglyMeasurable

/-- The increment's own strict natural history is contained in the data prefix. -/
theorem qChiFixedFluctuation_history_le_past (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    priorIncrementSigma (qChiFixedFluctuationIncrement M v η T u s a) t ≤ qPastSigma T t := by
  apply iSup₂_le
  intro j hj
  exact ((qChiFixedFluctuation_strong_nextPast M v η T u j s a).measurable.mono
    (qPastSigma_mono T (j+1) t (by omega)) le_rfl).comap_le

/-- Conditional mean zero persists under the increment-generated history. -/
theorem qChiFixedFluctuation_condExp_natural_zero (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    (qSamplingLaw M T)[qChiFixedFluctuationIncrement M v η T u s a t |
      priorIncrementSigma (qChiFixedFluctuationIncrement M v η T u s a) t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  exact qCondExp_zero_of_smaller M T _ _ (qChiFixedFluctuation_history_le_past M v η T u t s a)
    (qPastSigma_le T t) _ (qChiFixedFluctuation_condExp_zero M v η T u t s a)

/-- Active-layer conditional square remains the deterministic true-row variance
with its exact deterministic squared weight under the smaller history. -/
theorem qChiFixedFluctuation_condExp_natural_sq (M : DiscountedMDP State Action) (v : State → ℝ) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action)
    (h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u) :
    (qSamplingLaw M T)[(fun data ↦ (qChiFixedFluctuationIncrement M v η T u s a t data)^2) |
      priorIncrementSigma (qChiFixedFluctuationIncrement M v η T u s a) t] =ᵐ[qSamplingLaw M T]
      fun _ ↦ (M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (v) := by
  let m := priorIncrementSigma (qChiFixedFluctuationIncrement M v η T u s a) t
  have hle := qChiFixedFluctuation_history_le_past M v η T u t s a
  have htower := condExp_condExp_of_le (μ := qSamplingLaw M T)
    (f := fun data ↦ (qChiFixedFluctuationIncrement M v η T u s a t data)^2) hle (qPastSigma_le T t)
  have hc := condExp_congr_ae (m := m) (qChiFixedFluctuation_condExp_sq M v η T u t s a h)
  have hconst := condExp_const (μ := qSamplingLaw M T) (hle.trans (qPastSigma_le T t))
    ((M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (v))
  exact htower.symm.trans (hc.trans (Filter.Eventually.of_forall fun data ↦ by rw [hconst]))


end StatisticalRL.QLearning
