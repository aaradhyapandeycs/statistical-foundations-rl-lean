import Formalization.Generative.GenerativeLowerBoundQRandomOutputLaw
import Formalization.Generative.GenerativeLowerBoundOverlapTesting

/-! Randomized binary testing with one common model-independent kernel. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Any common binary kernel retains the baseline-versus-mixture overlap
lower bound on the *sum* of the two actual joint-law errors. -/
theorem finiteBinaryKernel_overlap_le_error_sum {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : X → PMF Bool) :
    finiteOverlap μ ν ≤
      (finiteKernelJointLaw μ κ).real {z | z.2 = true} +
      (finiteKernelJointLaw ν κ).real {z | z.2 = false} := by
  classical
  let σ : Measure (X → Bool) := (finiteKernelSeed κ).toMeasure
  haveI : IsProbabilityMeasure σ := by dsimp [σ]; infer_instance
  let E₀ : Set (X × (X → Bool)) := {z | z.2 z.1 = true}
  let E₁ : Set (X × (X → Bool)) := {z | z.2 z.1 = false}
  have h₀ : (finiteKernelJointLaw μ κ).real {z | z.2 = true} =
      (independentSeedLaw μ σ).real E₀ := by
    rw [← finiteKernelSeed_joint_law μ κ]
    simp only [measureReal_def, Measure.map_apply (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    rfl
  have h₁ : (finiteKernelJointLaw ν κ).real {z | z.2 = false} =
      (independentSeedLaw ν σ).real E₁ := by
    rw [← finiteKernelSeed_joint_law ν κ]
    simp only [measureReal_def, Measure.map_apply (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    rfl
  rw [h₀, h₁, independentSeedLaw_real_event, independentSeedLaw_real_event]
  let w (f : X → Bool) : ℝ := σ.real {f}
  have hw (f : X → Bool) : 0 ≤ w f := measureReal_nonneg
  have hw1 : ∑ f, w f = 1 := by
    dsimp [w]
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have htest (f : X → Bool) := finiteOverlap_le_test_error_sum μ ν f
  have hs := Finset.sum_le_sum (fun f (_ : f ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_right (htest f) (hw f))
  rw [← Finset.mul_sum, hw1, mul_one] at hs
  simpa only [E₀, E₁, Set.mem_setOf_eq, add_mul, Finset.sum_add_distrib] using hs

end StatisticalRL.GenerativeLowerBound
