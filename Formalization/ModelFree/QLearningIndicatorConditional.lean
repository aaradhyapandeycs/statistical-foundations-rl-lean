import Formalization.ModelFree.QLearningConditionalCentering

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

noncomputable def qFreshSigma (T t : ℕ) (ht : t < T) (s : State) (a : Action) :
    MeasurableSpace (QSamples State Action T) :=
  MeasurableSpace.comap (fun data : QSamples State Action T ↦ data ((s,a), ⟨t,ht⟩)) inferInstance

theorem qFreshSigma_indep_past (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) :
    Indep (qFreshSigma T t ht s a) (qPastSigma T t) (qSamplingLaw M T) := by
  simpa [qFreshSigma, qPastSigma, IndepFun_iff_Indep] using
    (qPast_indep_fresh M T t ht s a).symm

theorem qFreshIndicator_strong (T t : ℕ) (ht : t < T) (s : State) (a : Action) (x : State) :
    StronglyMeasurable[qFreshSigma T t ht s a] (qFreshIndicator T t ht s a x) := by
  classical
  let f : State → ℝ := fun y ↦ if y = x then 1 else 0
  have hf : Measurable f := measurable_of_countable _
  have hg : Measurable[qFreshSigma T t ht s a]
      (fun data : QSamples State Action T ↦ data ((s,a), ⟨t,ht⟩)) := comap_measurable _
  exact (hf.comp hg).stronglyMeasurable

end StatisticalRL.QLearning
