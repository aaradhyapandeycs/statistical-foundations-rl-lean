import Formalization.Probability.EmpiricalHoeffdingRandomFamily
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Borel measurable finite vector families

Represent an unordered finite family by any injective finite enumeration. The
quotient σ-algebra makes a family event measurable exactly when its preimage
under every finite enumeration is Borel measurable. We show the Hoeffding
family tests are measurable in this representation. Independence is imposed on
the unordered family, not on an enumeration or on the ordered sample.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance randomFamilyBorelStateMeasurable : MeasurableSpace State := ⊤

/-- A duplicate-free finite list of state vectors, encoded as a finite tuple. -/
abbrev FamilyEnumeration (n : ℕ) :=
  {v : Fin n → State → ℝ // Function.Injective v}

/-- Forget the ordering of an injective finite tuple. -/
noncomputable def enumerationFamily (n : ℕ) (v : FamilyEnumeration (State := State) n) :
    Finset (State → ℝ) := by
  classical
  exact Finset.univ.image v.1

@[simp]
theorem enumerationFamily_card (n : ℕ) (v : FamilyEnumeration (State := State) n) :
    (enumerationFamily n v).card = n := by
  classical
  simp [enumerationFamily, Finset.card_image_of_injective _ v.2]

/-- Every finite family has an injective enumeration, including the empty one. -/
theorem enumerationFamily_surjective (family : Finset (State → ℝ)) :
    ∃ (n : ℕ) (v : FamilyEnumeration (State := State) n), enumerationFamily n v = family := by
  classical
  let e := family.equivFin.symm
  have hi : Function.Injective (fun i ↦ ((e i : family) : State → ℝ)) := by
    intro i j h
    exact e.injective (Subtype.ext h)
  refine ⟨family.card, ⟨fun i ↦ ((e i : family) : State → ℝ), hi⟩, ?_⟩
  ext V
  simp only [enumerationFamily, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hV
    refine ⟨family.equivFin ⟨V, hV⟩, ?_⟩
    simp [e]

/-- Duplicate-free tuples form a Borel subset of the ordinary finite tuple
space. -/
theorem measurableSet_injectiveEnumeration (n : ℕ) :
    MeasurableSet {v : Fin n → State → ℝ | Function.Injective v} := by
  classical
  have heq : {v : Fin n → State → ℝ | Function.Injective v} =
      ⋂ i : Fin n, ⋂ j : Fin n, {v : Fin n → State → ℝ | v i = v j → i = j} := by
    ext v
    simp [Function.Injective]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : i = j
  · simp [h]
  · have heq : MeasurableSet {v : Fin n → State → ℝ | v i = v j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    have hne : MeasurableSet {v : Fin n → State → ℝ | v i ≠ v j} := heq.compl
    convert hne using 1
    ext v
    simp only [Set.mem_setOf_eq]
    simp [h]

/-- The quotient σ-algebra of all Borel-measurable injective finite tuples,
forgetting enumeration order. The disjoint union over all n gives every finite
cardinality, including the empty family. -/
noncomputable def finiteFamilyBorel : MeasurableSpace (Finset (State → ℝ)) :=
  ⨅ n : ℕ, MeasurableSpace.map (enumerationFamily (State := State) n) inferInstance

/-- Each finite Borel tuple defines a measurable unordered family. -/
theorem measurable_enumerationFamily (n : ℕ) :
    @Measurable (FamilyEnumeration (State := State) n) (Finset (State → ℝ))
      inferInstance finiteFamilyBorel (enumerationFamily n) := by
  apply Measurable.of_le_map
  exact iInf_le (fun m : ℕ ↦ MeasurableSpace.map (enumerationFamily (State := State) m)
    inferInstance) n

/-- A family event is quotient-Borel precisely when its inverse image is
measurable in each ordinary finite Borel tuple space. -/
theorem finiteFamilyBorel_measurableSet_iff (A : Set (Finset (State → ℝ))) :
    @MeasurableSet (Finset (State → ℝ)) finiteFamilyBorel A ↔
      ∀ n : ℕ, MeasurableSet ((enumerationFamily (State := State) n) ⁻¹' A) := by
  exact MeasurableSpace.measurableSet_iInf

/-- The source nonnegativity test is measurable on each Borel tuple space. -/
theorem enumerationFamily_nonneg_measurable (n : ℕ) :
    MeasurableSet {v : FamilyEnumeration (State := State) n |
      ∀ V ∈ enumerationFamily n v, ∀ s, 0 ≤ V s} := by
  classical
  have heq : {v : FamilyEnumeration (State := State) n |
      ∀ V ∈ enumerationFamily n v, ∀ s, 0 ≤ V s} =
      ⋂ i : Fin n, ⋂ s : State, {v | 0 ≤ v.1 i s} := by
    ext v
    simp [enumerationFamily]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro s
  exact measurableSet_le measurable_const ((measurable_pi_apply s).comp
    ((measurable_pi_apply i).comp measurable_subtype_coe))

/-- Each actual empirical-row Hoeffding failure test is measurable on the
ordinary Borel space of injectively enumerated finite vector tuples. -/
theorem enumerationFamily_bad_measurable (d : FiniteDistribution State) (N : ℕ) (δ : ℝ)
    (row : FiniteDistribution State) (n : ℕ) :
    MeasurableSet {v : FamilyEnumeration (State := State) n |
      familyBadAt d N δ (enumerationFamily n v) row} := by
  classical
  have heq : {v : FamilyEnumeration (State := State) n |
      familyBadAt d N δ (enumerationFamily n v) row} =
      ⋃ i : Fin n, {v | familyRadius N n δ (v.1 i) <
        |row.expectation (v.1 i) - d.expectation (v.1 i)|} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, familyBadAt, enumerationFamily_card]
    simp [enumerationFamily]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  have hv : Measurable (fun v : FamilyEnumeration (State := State) n ↦ v.1 i) :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  have heval (q : FiniteDistribution State) :
      Measurable (fun v : FamilyEnumeration (State := State) n ↦ q.expectation (v.1 i)) := by
    unfold FiniteDistribution.expectation
    exact Finset.measurable_sum _ (fun s _ ↦ measurable_const.mul ((measurable_pi_apply s).comp hv))
  unfold familyRadius
  exact measurableSet_lt (hv.norm.mul measurable_const) ((heval row).sub (heval d)).abs

/-- The family-test σ-algebra is contained in the quotient Borel σ-algebra. -/
theorem familyTestSpace_le_finiteFamilyBorel (d : FiniteDistribution State) (N : ℕ) (δ : ℝ) :
    d.familyTestSpace N δ ≤ finiteFamilyBorel (State := State) := by
  unfold familyTestSpace finiteFamilyBorel
  apply MeasurableSpace.generateFrom_le
  intro t ht
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((enumerationFamily (State := State) n) ⁻¹' t)
  rcases ht with hnonneg | ⟨row, rfl⟩
  · simp only [Set.mem_singleton_iff] at hnonneg
    subst t
    exact enumerationFamily_nonneg_measurable n
  · exact enumerationFamily_bad_measurable d N δ row n

/-- Hoeffding's strict source bound for a random unordered family measurable
in the quotient Borel σ-algebra, independent only of the empirical row. -/
theorem randomBorelFamily_empiricalRow_success_gt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (draw : Ω → Fin N → State) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure N)
    (family : Ω → Finset (State → ℝ))
    (hfamily : letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
      Measurable family)
    (hindep : letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
      letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ)
    (hV : ∀ᵐ ω ∂μ, ∀ V ∈ family ω, ∀ s, 0 ≤ V s) :
    1 - δ < μ.real {ω | ∀ V ∈ family ω,
      |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family ω).card / δ) / (2 * N))} := by
  have hle := d.familyTestSpace_le_finiteFamilyBorel N δ
  have hfamily' : letI : MeasurableSpace (Finset (State → ℝ)) := d.familyTestSpace N δ
      Measurable family := hfamily.mono le_rfl hle
  have hindep' : letI : MeasurableSpace (Finset (State → ℝ)) := d.familyTestSpace N δ
      letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ := by
    have hid : @Measurable (Finset (State → ℝ)) (Finset (State → ℝ))
        finiteFamilyBorel (d.familyTestSpace N δ) id := measurable_id'' hle
    simpa only [Function.id_comp] using hindep.comp hid measurable_id
  exact d.randomFiniteFamily_empiricalRow_success_gt_vectorSigma μ N hN δ hδ hδ1
    draw hdraw hlaw family hfamily' hindep' hV

end StatisticalRL.FiniteDistribution
