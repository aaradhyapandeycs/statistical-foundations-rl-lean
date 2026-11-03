import Formalization.ModelFree.QLearningConditionalMoments

/-! Prefix/current-layer independence and predictability for the Q-learning sampling law. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- All state/action coordinates observed at a single zero-based layer. -/
noncomputable def qLayerIndices (T t : ℕ) : Finset ((State × Action) × Fin T) :=
  Finset.univ.filter fun i ↦ i.2.val = t

noncomputable def qLayerData (T t : ℕ) (data : QSamples State Action T) :
    (i : qLayerIndices (State := State) (Action := Action) T t) → State :=
  fun i ↦ data i.1

noncomputable def qLayerSigma (T t : ℕ) : MeasurableSpace (QSamples State Action T) :=
  MeasurableSpace.comap (qLayerData (State := State) (Action := Action) T t) inferInstance

/-- Entire past and entire current layer are disjoint even when t≥T. -/
theorem qPast_disjoint_layer (T t : ℕ) :
    Disjoint (qPastIndices (State := State) (Action := Action) T t)
      (qLayerIndices (State := State) (Action := Action) T t) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact (Nat.ne_of_lt hi') hj'

/-- Actual joint product law separates the full past code from the new layer. -/
theorem qPast_indep_layer (M : DiscountedMDP State Action) (T t : ℕ) :
    IndepFun (qPastData (State := State) (Action := Action) T t)
      (qLayerData (State := State) (Action := Action) T t) (qSamplingLaw M T) := by
  exact iIndepFun.indepFun_finset _ _ (qPast_disjoint_layer T t)
    (qSamplingLaw_independent M T) (fun i ↦ measurable_pi_apply i)

/-- Independence at the sigma-algebra level, in conditional-expectation order. -/
theorem qLayerSigma_indep_pastSigma (M : DiscountedMDP State Action) (T t : ℕ) :
    Indep (qLayerSigma (State := State) (Action := Action) T t)
      (qPastSigma (State := State) (Action := Action) T t) (qSamplingLaw M T) := by
  exact (qPast_indep_layer M T t).symm

/-- The entire iterate is measurable relative to precisely the strict prefix. -/
theorem qIterate_measurable_past (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t ≤ T) (Q₀ : State → Action → ℝ) :
    Measurable[qPastSigma T t] (fun data : QSamples State Action T ↦
      qLearningIterate M η (qSamplesExtend M T data) Q₀ t) := by
  let F := fun code ↦ qLearningIterate M η
    (qSamplesExtend M T (qCompletePast M T t code)) Q₀ t
  have hF : Measurable F := measurable_of_countable _
  have hpast : Measurable[qPastSigma T t] (qPastData (State := State) (Action := Action) T t) :=
    comap_measurable _
  have heq : F ∘ qPastData T t = fun data : QSamples State Action T ↦
      qLearningIterate M η (qSamplesExtend M T data) Q₀ t := by
    funext data
    exact (qIterate_factors_past M η T t ht Q₀ data).symm
  rw [← heq]
  exact hF.comp hpast

/-- Each scalar value coordinate is strongly measurable in the strict prefix. -/
theorem qValue_stronglyMeasurable_past (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t ≤ T) (Q₀ : State → Action → ℝ) (s : State) :
    StronglyMeasurable[qPastSigma T t]
      (fun data : QSamples State Action T ↦ qValueBefore M η T t Q₀ data s) := by
  let F := fun code ↦ qLearningValue M (qLearningIterate M η
    (qSamplesExtend M T (qCompletePast M T t code)) Q₀ t) s
  have hF : Measurable F := measurable_of_countable _
  have hpast : Measurable[qPastSigma T t] (qPastData (State := State) (Action := Action) T t) :=
    comap_measurable _
  have heq : F ∘ qPastData T t = fun data : QSamples State Action T ↦
      qValueBefore M η T t Q₀ data s := by
    funext data
    simp only [F, Function.comp_apply, qValueBefore]
    rw [qIterate_factors_past M η T t ht Q₀ data]
  rw [← heq]
  exact (hF.comp hpast).stronglyMeasurable

end StatisticalRL.QLearning
