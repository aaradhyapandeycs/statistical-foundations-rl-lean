import Formalization.ModelFree.QLearningNaturalHistory

/-! Adapted Q-learning increments, history inclusion and the conditional-variance tower. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- The observed increment is unchanged by completing its j+1 prefix. -/
theorem qRowIncrement_factors_nextPast (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T j : ℕ) (hj : j < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (data : QSamples State Action T) :
    qRowIncrement M η T j hj Q₀ s a data =
      qRowIncrement M η T j hj Q₀ s a
        (qCompletePast M T (j+1) (qPastData T (j+1) data)) := by
  have hiter : qLearningIterate M η (qSamplesExtend M T data) Q₀ j =
      qLearningIterate M η
        (qSamplesExtend M T (qCompletePast M T (j+1) (qPastData T (j+1) data))) Q₀ j := by
    apply qIterate_eq_of_samples_agree
    intro k hk hkj x b
    have hkT : k-1 < T := by omega
    have hmem : ((x,b), (⟨k-1,hkT⟩ : Fin T)) ∈
        qPastIndices (State := State) (Action := Action) T (j+1) := by
      simp [qPastIndices]
      omega
    have h₁ := qSamplesExtend_succ M T data (k-1) hkT x b
    have h₂ := qSamplesExtend_succ M T (qCompletePast M T (j+1) (qPastData T (j+1) data))
      (k-1) hkT x b
    have heq : qCompletePast M T (j+1) (qPastData T (j+1) data) ((x,b), ⟨k-1,hkT⟩) =
        data ((x,b), ⟨k-1,hkT⟩) := by simp [qCompletePast, qPastData, hmem]
    have hh := h₁.trans (heq.symm.trans h₂.symm)
    simpa only [show k-1+1 = k by omega] using hh
  have hmem : ((s,a), (⟨j,hj⟩ : Fin T)) ∈
      qPastIndices (State := State) (Action := Action) T (j+1) := by simp [qPastIndices]
  have hfresh : qCompletePast M T (j+1) (qPastData T (j+1) data) ((s,a), ⟨j,hj⟩) =
      data ((s,a), ⟨j,hj⟩) := by simp [qCompletePast, qPastData, hmem]
  simp [qRowIncrement, qValueBefore, ← hiter, hfresh]

/-- Increment j is observed after the whole layer j enters the history. -/
theorem qPaddedIncrement_strong_nextPast (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T j : ℕ) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    StronglyMeasurable[qPastSigma T (j+1)] (qPaddedIncrement M η T Q₀ s a j) := by
  classical
  by_cases hj : j < T
  · let F := fun code ↦ qRowIncrement M η T j hj Q₀ s a (qCompletePast M T (j+1) code)
    have hm : Measurable F := measurable_of_countable _
    have hp : Measurable[qPastSigma T (j+1)] (qPastData (State := State) (Action := Action) T (j+1)) :=
      comap_measurable _
    have heq : F ∘ qPastData T (j+1) = qPaddedIncrement M η T Q₀ s a j := by
      funext data
      simpa [F, qPaddedIncrement, hj] using (qRowIncrement_factors_nextPast M η T j hj Q₀ s a data).symm
    rw [← heq]
    exact (hm.comp hp).stronglyMeasurable
  · have hz : qPaddedIncrement M η T Q₀ s a j = 0 := by
      funext data
      simp [qPaddedIncrement, hj]
    rw [hz]
    exact stronglyMeasurable_zero

/-- The increment-generated strict past is contained in the actual sample prefix. -/
theorem qPriorIncrementSigma_le_past (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    priorIncrementSigma (qPaddedIncrement M η T Q₀ s a) t ≤ qPastSigma T t := by
  apply iSup₂_le
  intro j hj
  exact ((qPaddedIncrement_strong_nextPast M η T j Q₀ s a).measurable.mono
    (qPastSigma_mono T (j+1) t (by omega)) le_rfl).comap_le

/-- Conditional centering on the smaller increment-generated history. -/
theorem qPaddedIncrement_condExp_natural_zero (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    (qSamplingLaw M T)[qPaddedIncrement M η T Q₀ s a t |
      priorIncrementSigma (qPaddedIncrement M η T Q₀ s a) t] =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  classical
  by_cases ht : t < T
  · apply qCondExp_zero_of_smaller M T _ _ (qPriorIncrementSigma_le_past M η T t Q₀ s a)
      (qPastSigma_le T t)
    have hp : qPaddedIncrement M η T Q₀ s a t = qRowIncrement M η T t ht Q₀ s a := by
      funext data
      simp [qPaddedIncrement, ht]
    rw [hp]
    exact qRowIncrement_condExp_zero M η T t ht Q₀ s a
  · have hz : qPaddedIncrement M η T Q₀ s a t = 0 := by
      funext data
      simp [qPaddedIncrement, ht]
    rw [hz, condExp_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Tower transfer of the actual conditional square; the right-hand side is
still conditioned on the smaller history and is not simplified to the variance. -/
theorem qPaddedIncrement_condExp_sq_natural (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    (qSamplingLaw M T)[(fun data ↦ (qPaddedIncrement M η T Q₀ s a t data)^2) |
      priorIncrementSigma (qPaddedIncrement M η T Q₀ s a) t] =ᵐ[qSamplingLaw M T]
    (qSamplingLaw M T)[(fun data ↦ qRowVariance M s a (qValueBefore M η T t Q₀ data)) |
      priorIncrementSigma (qPaddedIncrement M η T Q₀ s a) t] := by
  have h := condExp_condExp_of_le (μ := qSamplingLaw M T)
    (f := fun data ↦ (qRowIncrement M η T t ht Q₀ s a data)^2)
    (qPriorIncrementSigma_le_past M η T t Q₀ s a) (qPastSigma_le T t)
  have hv := condExp_congr_ae (m := priorIncrementSigma (qPaddedIncrement M η T Q₀ s a) t)
    (qRowIncrement_condExp_sq M η T t ht Q₀ s a)
  simpa [qPaddedIncrement, ht] using h.symm.trans hv

end StatisticalRL.QLearning
