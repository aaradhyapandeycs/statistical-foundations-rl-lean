import Formalization.ModelFree.QLearningOptimalFluctuationMoments
import Formalization.ModelFree.QLearningIncrementCaps
import Formalization.Probability.FreedmanNaturalHistory

/-! Fixed-terminal source fluctuation natural history and active-layer caps. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptHistoryStateMeasurable : MeasurableSpace State := ⊤
local instance qOptHistoryActionMeasurable : MeasurableSpace Action := ⊤

/-- Fixed-terminal source increment factors through the prefix after layer t. -/
theorem qOptimalFluctuation_factors_nextPast (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) (data : QSamples State Action T) :
    qOptimalFluctuationIncrement M η T u s a t data =
      qOptimalFluctuationIncrement M η T u s a t
        (qCompletePast M T (t+1) (qPastData T (t+1) data)) := by
  classical
  by_cases ht : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u
  · have hmem : ((s,a), (⟨t,ht.1⟩ : Fin T)) ∈
        qPastIndices (State := State) (Action := Action) T (t+1) := by simp [qPastIndices]
    simp [qOptimalFluctuationIncrement, ht, qCompletePast, qPastData, hmem]
  · simp [qOptimalFluctuationIncrement, ht]

/-- Every increment is measurable once its own layer has been observed. -/
theorem qOptimalFluctuation_strong_nextPast (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    StronglyMeasurable[qPastSigma T (t+1)] (qOptimalFluctuationIncrement M η T u s a t) := by
  let F := fun code ↦ qOptimalFluctuationIncrement M η T u s a t (qCompletePast M T (t+1) code)
  have hm : Measurable F := measurable_of_countable _
  have hp : Measurable[qPastSigma T (t+1)] (qPastData (State := State) (Action := Action) T (t+1)) :=
    comap_measurable _
  have heq : F ∘ qPastData T (t+1) = qOptimalFluctuationIncrement M η T u s a t := by
    funext data
    exact (qOptimalFluctuation_factors_nextPast M η T u t s a data).symm
  rw [← heq]
  exact (hm.comp hp).stronglyMeasurable

/-- The increment's own strict natural history is contained in the data prefix. -/
theorem qOptimalFluctuation_history_le_past (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    priorIncrementSigma (qOptimalFluctuationIncrement M η T u s a) t ≤ qPastSigma T t := by
  apply iSup₂_le
  intro j hj
  exact ((qOptimalFluctuation_strong_nextPast M η T u j s a).measurable.mono
    (qPastSigma_mono T (j+1) t (by omega)) le_rfl).comap_le

/-- Conditional mean zero persists under the increment-generated history. -/
theorem qOptimalFluctuation_condExp_natural_zero (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action) :
    (qSamplingLaw M T)[qOptimalFluctuationIncrement M η T u s a t |
      priorIncrementSigma (qOptimalFluctuationIncrement M η T u s a) t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  exact qCondExp_zero_of_smaller M T _ _ (qOptimalFluctuation_history_le_past M η T u t s a)
    (qPastSigma_le T t) _ (qOptimalFluctuation_condExp_zero M η T u t s a)

/-- Active-layer conditional square remains the deterministic true-row variance
with its exact deterministic squared weight under the smaller history. -/
theorem qOptimalFluctuation_condExp_natural_sq (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action)
    (h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u) :
    (qSamplingLaw M T)[(fun data ↦ (qOptimalFluctuationIncrement M η T u s a t data)^2) |
      priorIncrementSigma (qOptimalFluctuationIncrement M η T u s a) t] =ᵐ[qSamplingLaw M T]
      fun _ ↦ (M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (qTrueOptimalValue M) := by
  let m := priorIncrementSigma (qOptimalFluctuationIncrement M η T u s a) t
  have hle := qOptimalFluctuation_history_le_past M η T u t s a
  have htower := condExp_condExp_of_le (μ := qSamplingLaw M T)
    (f := fun data ↦ (qOptimalFluctuationIncrement M η T u s a t data)^2) hle (qPastSigma_le T t)
  have hc := condExp_congr_ae (m := m) (qOptimalFluctuation_condExp_sq M η T u t s a h)
  have hconst := condExp_const (μ := qSamplingLaw M T) (hle.trans (qPastSigma_le T t))
    ((M.discount * qPositiveWeight η u (t+1))^2 * qRowVariance M s a (qTrueOptimalValue M))
  exact htower.symm.trans (hc.trans (Filter.Eventually.of_forall fun data ↦ by rw [hconst]))

/-- The exact true optimal row variance has a deterministic H² bound. -/
theorem qOptimal_rowVariance_le (M : DiscountedMDP State Action) (s : State) (a : Action) :
    qRowVariance M s a (qTrueOptimalValue M) ≤ M.effectiveHorizon^2 :=
  qRowVariance_le_sq M s a _ _ M.effectiveHorizon_nonneg (qTrueOptimalValue_bounds M)

/-- Under source rate bounds, active increment magnitude is bounded by its
nonnegative deterministic source weight times the effective horizon. -/
theorem qOptimalFluctuation_abs_le (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u t : ℕ) (s : State) (a : Action)
    (h : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u)
    (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1)
    (data : QSamples State Action T) :
    |qOptimalFluctuationIncrement M η T u s a t data| ≤
      M.discount * qPositiveWeight η u (t+1) * M.effectiveHorizon := by
  have hw : 0 ≤ M.discount * qPositiveWeight η u (t+1) :=
    mul_nonneg M.discount_nonneg (qPositiveWeight_nonneg η u (t+1) (by omega) h.2.2 hη)
  have hb := qRow_abs_centered_le (M.transition s a) (qTrueOptimalValue M)
    M.effectiveHorizon (qTrueOptimalValue_bounds M) (data ((s,a), ⟨t,h.1⟩))
  simpa [qOptimalFluctuationIncrement, h, abs_mul, abs_of_nonneg hw] using mul_le_mul_of_nonneg_left hb hw

/- Pending: inactive-layer zero statement, global bound by an explicit maximum
weight, finite sum of exact conditional variances and late-weight source lemma,
weighted sum/source indexing match, and Freedman/union probability. All proofs
above await focused compilation and independent source review. -/
end StatisticalRL.QLearning
