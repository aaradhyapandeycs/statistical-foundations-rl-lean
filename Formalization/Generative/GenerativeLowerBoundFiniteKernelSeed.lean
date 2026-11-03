import Formalization.Generative.GenerativeLowerBoundRandomSeed
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Any finite kernel is realized by one independent random function. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

section
variable {X Y : Type*} [Fintype X] [Fintype Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Draw one output independently for each possible observation. The seed is
one function X → Y; its PMF may have arbitrary real-valued atom weights. -/
noncomputable def finiteKernelSeed (κ : X → PMF Y) : PMF (X → Y) :=
  (Measure.pi (fun x ↦ (κ x).toMeasure)).toPMF

/-- The seed law at each coordinate is exactly the prescribed kernel output
law for that observation, including zero-probability outputs. -/
theorem finiteKernelSeed_eval_marginal (κ : X → PMF Y) (x : X) :
    (finiteKernelSeed κ).toMeasure.map (fun f ↦ f x) = (κ x).toMeasure := by
  unfold finiteKernelSeed
  rw [Measure.toPMF_toMeasure]
  exact (measurePreserving_eval (fun x ↦ (κ x).toMeasure) x).map_eq

/-- The resulting rule uses the same seed law for every hypothesis. -/
def finiteKernelSeedEstimator (f : X → Y) (x : X) : Y := f x

/-- The actual observation/output law obtained from the kernel itself. -/
noncomputable def finiteKernelJointLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : X → PMF Y) : Measure (X × Y) :=
  (μ.toPMF.bind fun x ↦ (κ x).map (fun y ↦ (x, y))).toMeasure

/-- A common independent random-function seed realizes the entire joint
observation/output law, not merely its output marginal. -/
theorem finiteKernelSeed_joint_law (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : X → PMF Y) :
    (independentSeedLaw μ (finiteKernelSeed κ).toMeasure).map
      (fun z : X × (X → Y) ↦ (z.1, z.2 z.1)) = finiteKernelJointLaw μ κ := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  unfold independentSeedLaw
  rw [Measure.prod_apply (Set.to_countable _).measurableSet, lintegral_fintype]
  rw [finiteKernelJointLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.bind_apply, tsum_fintype]
  have hsec (z : X) : (finiteKernelSeed κ).toMeasure
      ((Prod.mk z) ⁻¹' ((fun z : X × (X → Y) ↦ (z.1, z.2 z.1)) ⁻¹' {(x, y)})) =
      if z = x then (κ x) y else 0 := by
    by_cases hz : z = x
    · subst z
      have h := congrArg (fun ρ : Measure Y ↦ ρ {y}) (finiteKernelSeed_eval_marginal κ x)
      dsimp only at h
      rw [Measure.map_apply (measurable_pi_apply x) (measurableSet_singleton _),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
      have hs : (Prod.mk x) ⁻¹' ((fun z : X × (X → Y) ↦ (z.1, z.2 z.1)) ⁻¹' {(x, y)}) =
          (fun f : X → Y ↦ f x) ⁻¹' {y} := by ext f; simp
      simp only [if_pos rfl]
      rw [hs]
      exact h
    · simp [hz]
  simp_rw [hsec]
  simp [PMF.map_apply, tsum_fintype, Measure.toPMF_apply, ite_and, mul_comm]

end
end StatisticalRL.GenerativeLowerBound
