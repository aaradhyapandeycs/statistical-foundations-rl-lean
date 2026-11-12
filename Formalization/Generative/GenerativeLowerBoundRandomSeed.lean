import Formalization.Generative.GenerativeLowerBoundPolicyGap
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Independent finite random seed and averaging of actual error events. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance randomSeedStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance randomSeedFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Product sampling law records an independent, hypothesis-independent
random seed whose law is chosen once and shared by every model. -/
noncomputable def independentSeedLaw {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (σ : Measure Ξ) : Measure (Ω × Ξ) := μ.prod σ

/-- For finite seed space, the actual joint probability of any event is the
seed-probability-weighted average of its fixed-seed sample probabilities. -/
theorem independentSeedLaw_real_event {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (μ : Measure Ω) (σ : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure σ]
    (E : Set (Ω × Ξ)) :
    (independentSeedLaw μ σ).real E =
      ∑ r, μ.real {x | (x, r) ∈ E} * σ.real {r} := by
  classical
  rw [measureReal_def, independentSeedLaw, Measure.prod_apply_symm (Set.to_countable E).measurableSet,
    lintegral_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, measureReal_def]
    rfl
  · intro r _
    exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top σ _)

end StatisticalRL.GenerativeLowerBound
