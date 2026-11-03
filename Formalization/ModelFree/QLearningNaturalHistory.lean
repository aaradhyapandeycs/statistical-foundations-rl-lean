import Formalization.ModelFree.QLearningConditionalIncrement
import Formalization.Probability.FreedmanNaturalHistory

/-! Actual Q-learning increments and their strict natural history. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- Exactly T increments; after the final observed layer, pad with zero. -/
noncomputable def qPaddedIncrement (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T : ℕ) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (t : ℕ) (data : QSamples State Action T) : ℝ :=
  if ht : t < T then qRowIncrement M η T t ht Q₀ s a data else 0

/-- The prefix containing u layers restricts canonically to the first t layers. -/
noncomputable def qRestrictPast (T t u : ℕ) (htu : t ≤ u)
    (code : (i : qPastIndices (State := State) (Action := Action) T u) → State) :
    (i : qPastIndices (State := State) (Action := Action) T t) → State :=
  fun i ↦ code ⟨i.1, by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp i.2).2 htu⟩⟩

/-- Strict sample histories grow monotonically. -/
theorem qPastSigma_mono (T t u : ℕ) (htu : t ≤ u) :
    qPastSigma (State := State) (Action := Action) T t ≤ qPastSigma T u := by
  have hm : Measurable (qRestrictPast (State := State) (Action := Action) T t u htu) :=
    measurable_of_countable _
  have hp : Measurable[qPastSigma T u] (qPastData (State := State) (Action := Action) T u) :=
    comap_measurable _
  have hcomp := hm.comp hp
  have heq : qRestrictPast T t u htu ∘ qPastData T u =
      qPastData (State := State) (Action := Action) T t := by
    funext data i
    rfl
  rw [heq] at hcomp
  exact hcomp.comap_le

/-- Pure tower step: a zero conditional mean on a larger actual history remains
zero on any smaller history. The finite actual sampling law ensures integrability. -/
theorem qCondExp_zero_of_smaller (M : DiscountedMDP State Action) (T : ℕ)
    (m₁ m₂ : MeasurableSpace (QSamples State Action T))
    (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ (MeasurableSpace.pi : MeasurableSpace (QSamples State Action T)))
    (f : QSamples State Action T → ℝ)
    (hcenter : (qSamplingLaw M T)[f | m₂] =ᵐ[qSamplingLaw M T] fun _ ↦ 0) :
    (qSamplingLaw M T)[f | m₁] =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  have htower := condExp_condExp_of_le (μ := qSamplingLaw M T) (f := f) h₁₂ h₂
  have hzero := condExp_congr_ae (m := m₁) hcenter
  have hz : (qSamplingLaw M T)[(0 : QSamples State Action T → ℝ) | m₁] = 0 := condExp_zero
  exact htower.symm.trans (hzero.trans (Filter.Eventually.of_forall fun x ↦ by change (qSamplingLaw M T)[(0 : QSamples State Action T → ℝ) | m₁] x = 0; rw [hz]; rfl))

/- Adaptation and natural-history moment transfer are established in QLearningHistoryAdaptation. -/
end StatisticalRL.QLearning
