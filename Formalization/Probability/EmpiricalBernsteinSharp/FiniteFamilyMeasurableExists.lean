import Formalization.Probability.RandomFamilyBorel

/-! Private uncompiled generic measurability bridge for an existential event
over the project's Borel finite-family representation. -/
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]

/-- The same bridge when the test also depends on the family's cardinality. -/
theorem finiteFamilyBorel_exists_card_measurable (bad : ℕ → (State → ℝ) → Prop)
    (hbad : ∀ n, MeasurableSet {V | bad n V}) :
    letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
    MeasurableSet {family : Finset (State → ℝ) | ∃ V ∈ family, bad family.card V} := by
  classical
  apply (finiteFamilyBorel_measurableSet_iff _).2
  intro n
  have heq : {v : FamilyEnumeration (State := State) n |
      ∃ V ∈ enumerationFamily n v, bad (enumerationFamily n v).card V} =
      ⋃ i : Fin n, {v | bad n (v.1 i)} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, enumerationFamily_card]
    simp [enumerationFamily]
  change MeasurableSet {v : FamilyEnumeration (State := State) n |
      ∃ V ∈ enumerationFamily n v, bad (enumerationFamily n v).card V}
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  exact (hbad n).preimage ((measurable_pi_apply i).comp measurable_subtype_coe)

end StatisticalRL.FiniteDistribution
