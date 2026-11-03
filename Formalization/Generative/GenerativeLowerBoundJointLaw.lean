import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing
import Mathlib.Probability.UniformOn
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Actual finite uniform-prior hypothesis/observation laws for Fano. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

section
variable {I Ω : Type*} [Fintype I] [Nonempty I] [Fintype Ω]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The actual uniform probability measure on the finite hypothesis space. -/
noncomputable def finiteHypothesisPrior : Measure I := uniformOn Set.univ

instance finiteHypothesisPrior_probability : IsProbabilityMeasure (finiteHypothesisPrior : Measure I) := by
  unfold finiteHypothesisPrior
  exact uniformOn_isProbabilityMeasure (Set.toFinite _) Set.univ_nonempty

/-- Actual joint hypothesis/observation measure: first draw a uniform index,
then draw its own observation law. All laws are on one common sample space. -/
noncomputable def finiteJointLaw (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] :
    Measure (I × Ω) :=
  ((finiteHypothesisPrior : Measure I).toPMF.bind fun i ↦
    (P i).toPMF.map (fun x ↦ (i, x))).toMeasure

instance finiteJointLaw_probability (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] : IsProbabilityMeasure (finiteJointLaw P) := by
  unfold finiteJointLaw
  infer_instance

/-- Common-baseline joint law, with the same uniform prior. -/
noncomputable def finiteBaselineJointLaw (Q : Measure Ω) [IsProbabilityMeasure Q] :
    Measure (I × Ω) := finiteJointLaw (fun _ ↦ Q)

instance finiteBaselineJointLaw_probability (Q : Measure Ω) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (finiteBaselineJointLaw (I := I) Q) := by
  unfold finiteBaselineJointLaw
  infer_instance

/-- Joint atom is the observation atom times the uniform prior mass. -/
theorem finiteJointLaw_singleton (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (i : I) (x : Ω) :
    finiteJointLaw P {(i, x)} = (Fintype.card I : ℝ≥0∞)⁻¹ * P i {x} := by
  classical
  rw [finiteJointLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.bind_apply, tsum_fintype]
  simp [PMF.map_apply, tsum_fintype, Measure.toPMF_apply, finiteHypothesisPrior,
    uniformOn_univ, eq_comm, Finset.mul_sum, ite_and]

/-- Interior observation laws give full support to the joint law. -/
theorem finiteJointLaw_atom_ne_zero (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i x, P i {x} ≠ 0)
    (z : I × Ω) : finiteJointLaw P {z} ≠ 0 := by
  classical
  rcases z with ⟨i, x⟩
  rw [finiteJointLaw_singleton]
  apply mul_ne_zero
  · exact ENNReal.inv_ne_zero.mpr (by simp)
  · exact hP i x

end
end StatisticalRL.GenerativeLowerBound
