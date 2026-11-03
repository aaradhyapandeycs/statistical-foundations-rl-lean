import Formalization.Probability.EmpiricalHoeffdingFamily
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Independent random finite families for empirical-row Hoeffding bounds -/

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance randomFamilyStateMeasurable : MeasurableSpace State := ⊤
local instance randomFamilyRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

/-- A deterministic family fails its source radius against an empirical row. -/
noncomputable def familyBadAt (d : FiniteDistribution State) (N : ℕ) (δ : ℝ)
    (family : Finset (State → ℝ)) (row : FiniteDistribution State) : Prop :=
  ∃ V ∈ family, familyRadius N family.card δ V < |row.expectation V - d.expectation V|

/-- The true law of the empirical row, including its finite support. -/
noncomputable def empiricalRowLaw (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N) :
    Measure (FiniteDistribution State) :=
  (d.sampleMeasure N).map (empiricalRow N hN)

instance empiricalRowLaw_isProbability (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (d.empiricalRowLaw N hN) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The finite set of every empirically attainable row. -/
noncomputable def empiricalRows (N : ℕ) (hN : 0 < N) : Finset (FiniteDistribution State) := by
  classical
  exact Finset.univ.image (empiricalRow N hN)

theorem empiricalRow_mem_empiricalRows (N : ℕ) (hN : 0 < N) (ω : Fin N → State) :
    empiricalRow N hN ω ∈ empiricalRows N hN := by
  classical
  exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩

/-- The exact empirical-row violation event has strict probability below δ,
including the empty family. -/
theorem empiricalRowLaw_familyBad_lt (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (family : Finset (State → ℝ)) (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    (d.empiricalRowLaw N hN).real {row | familyBadAt d N δ family row} < δ := by
  classical
  unfold empiricalRowLaw
  rw [measureReal_def, Measure.map_apply (measurable_of_countable _)
    (by exact MeasurableSpace.measurableSet_top)]
  change (d.sampleMeasure N).real {ω | familyBadAt d N δ family (empiricalRow N hN ω)} < δ
  by_cases hne : family.Nonempty
  · have hs := d.empiricalRow_family_success_gt N hN family hne δ hδ hδ1 hV
    let good : Set (Fin N → State) := {ω | ∀ V ∈ family,
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * family.card / δ) / (2 * N))}
    have hg : MeasurableSet good := (Set.to_countable good).measurableSet
    have heq : {ω | familyBadAt d N δ family (empiricalRow N hN ω)} = goodᶜ := by
      ext ω
      simp [familyBadAt, familyRadius_eq_source, good, not_le]
    rw [heq, measureReal_compl hg, probReal_univ]
    linarith
  · have hzero : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst family
    simp [familyBadAt, hδ]

section Joint

variable {Family : Type*} [MeasurableSpace Family]

/-- The measurable failure set on a family code and an attainable empirical row. -/
noncomputable def supportedFamilyBad (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ)) :
    Set (Family × FiniteDistribution State) :=
  ⋃ row ∈ empiricalRows N hN, {c | familyBadAt d N δ (family c) row} ×ˢ {row}

theorem measurableSet_supportedFamilyBad (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ))
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | familyBadAt d N δ (family c) row}) :
    MeasurableSet (supportedFamilyBad d N hN δ family) := by
  classical
  apply Finset.measurableSet_biUnion
  intro row hrow
  exact (hbad row hrow).prod (measurableSet_singleton row)

omit [MeasurableSpace Family] in
@[simp] theorem mem_supportedFamilyBad_empirical (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ))
    (c : Family) (ω : Fin N → State) :
    (c, empiricalRow N hN ω) ∈ supportedFamilyBad d N hN δ family ↔
      familyBadAt d N δ (family c) (empiricalRow N hN ω) := by
  classical
  simp [supportedFamilyBad, empiricalRow_mem_empiricalRows]

/-- Mixing independent empirical rows with arbitrary (possibly continuously
varying) family codes preserves strict failure probability below δ. -/
theorem product_supportedFamilyBad_lt (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ν : Measure Family) [IsProbabilityMeasure ν]
    (family : Family → Finset (State → ℝ))
    (hV : ∀ᵐ c ∂ν, ∀ V ∈ family c, ∀ s, 0 ≤ V s)
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | familyBadAt d N δ (family c) row}) :
    ν.prod (d.empiricalRowLaw N hN) (supportedFamilyBad d N hN δ family) < ENNReal.ofReal δ := by
  classical
  let ρ := d.empiricalRowLaw N hN
  let bad := supportedFamilyBad d N hN δ family
  have hm : MeasurableSet bad := measurableSet_supportedFamilyBad d N hN δ family hbad
  have hsec (c : Family) : ρ {r | (c, r) ∈ bad} =
      ρ {r | familyBadAt d N δ (family c) r} := by
    dsimp only [ρ, empiricalRowLaw]
    rw [Measure.map_apply (measurable_of_countable _) (by exact MeasurableSpace.measurableSet_top),
      Measure.map_apply (measurable_of_countable _) (by exact MeasurableSpace.measurableSet_top)]
    congr 1
    ext ω
    exact mem_supportedFamilyBad_empirical d N hN δ family c ω
  have hpoint : ∀ᵐ c ∂ν, ρ {r | (c, r) ∈ bad} < ENNReal.ofReal δ := by
    filter_upwards [hV] with c hc
    rw [hsec]
    have hb := d.empiricalRowLaw_familyBad_lt N hN δ hδ hδ1 (family c) hc
    apply (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mp
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using hb
  rw [Measure.prod_apply hm]
  have hfin : (∫⁻ c, ρ {r | (c, r) ∈ bad} ∂ν) ≠ ∞ := by
    have hle : (∫⁻ c, ρ {r | (c, r) ∈ bad} ∂ν) ≤
        (∫⁻ _c : Family, ENNReal.ofReal δ ∂ν) :=
      lintegral_mono_ae (hpoint.mono fun _ h ↦ h.le)
    have htop : (∫⁻ _c : Family, ENNReal.ofReal δ ∂ν) < ∞ := by simp
    exact ne_of_lt (lt_of_le_of_lt hle htop)
  have hlt := lintegral_strict_mono (IsProbabilityMeasure.ne_zero ν)
    measurable_const.aemeasurable hfin hpoint
  simpa using hlt

/-- A random finite family, independent of the *empirical row* (not required to
be independent of the ordered sample), satisfies the strict Hoeffding bound.
The family code may have an arbitrary measurable type and variable cardinality. -/
theorem randomFamily_empiricalRow_success_gt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (draw : Ω → Fin N → State) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure N)
    (code : Ω → Family) (hcode : Measurable code)
    (family : Family → Finset (State → ℝ))
    (hindep : IndepFun code (fun ω ↦ empiricalRow N hN (draw ω)) μ)
    (hV : ∀ᵐ ω ∂μ, ∀ V ∈ family (code ω), ∀ s, 0 ≤ V s)
    (hVmeas : MeasurableSet {c | ∀ V ∈ family c, ∀ s, 0 ≤ V s})
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | familyBadAt d N δ (family c) row}) :
    1 - δ < μ.real {ω | ∀ V ∈ family (code ω),
      |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family (code ω)).card / δ) / (2 * N))} := by
  classical
  let row : Ω → FiniteDistribution State := fun ω ↦ empiricalRow N hN (draw ω)
  have hrow : Measurable row := by
    change Measurable ((empiricalRow N hN) ∘ draw)
    exact (measurable_of_countable (empiricalRow N hN)).comp hdraw
  have hrowlaw : μ.map row = d.empiricalRowLaw N hN := by
    dsimp only [row, empiricalRowLaw]
    rw [← hlaw, Measure.map_map (measurable_of_countable _) hdraw]
    rfl
  let ν := μ.map code
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hcode.aemeasurable
  have hVν : ∀ᵐ c ∂ν, ∀ V ∈ family c, ∀ s, 0 ≤ V s :=
    (ae_map_iff hcode.aemeasurable hVmeas).mpr hV
  let bad := supportedFamilyBad d N hN δ family
  have hm : MeasurableSet bad := measurableSet_supportedFamilyBad d N hN δ family hbad
  have hpair : Measurable (fun ω ↦ (code ω, row ω)) := hcode.prodMk hrow
  have hindmap := (indepFun_iff_map_prod_eq_prod_map_map hcode.aemeasurable hrow.aemeasurable).mp hindep
  have hprob : μ ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) < ENNReal.ofReal δ := by
    rw [← Measure.map_apply hpair hm, hindmap, hrowlaw]
    exact d.product_supportedFamilyBad_lt N hN δ hδ hδ1 ν family hVν hbad
  have hreal : μ.real ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hprob
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using h
  have hmeas : MeasurableSet ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) := hm.preimage hpair
  have heq : ((fun ω ↦ (code ω, row ω)) ⁻¹' bad)ᶜ =
      {ω | ∀ V ∈ family (code ω),
        |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
          Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family (code ω)).card / δ) / (2 * N))} := by
    ext ω
    simp [bad, row, familyBadAt, familyRadius_eq_source, not_lt]
  have hc := measureReal_compl (μ := μ) hmeas
  rw [heq, probReal_univ] at hc
  exact (sub_lt_sub_left hreal 1).trans_eq hc.symm

/-- The smallest family σ-algebra needed to observe nonnegativity and every
empirical-row failure event, for the chosen sample size and confidence level. -/
noncomputable def familyTestSpace (d : FiniteDistribution State) (N : ℕ) (δ : ℝ) :
    MeasurableSpace (Finset (State → ℝ)) :=
  MeasurableSpace.generateFrom
    ({ {family | ∀ V ∈ family, ∀ s, 0 ≤ V s} } ∪
      Set.range (fun row : FiniteDistribution State ↦ {family | familyBadAt d N δ family row}))

theorem familyTestSpace_nonneg (d : FiniteDistribution State) (N : ℕ) (δ : ℝ) :
    @MeasurableSet (Finset (State → ℝ)) (familyTestSpace d N δ)
      {family | ∀ V ∈ family, ∀ s, 0 ≤ V s} := by
  apply MeasurableSpace.measurableSet_generateFrom
  exact Or.inl rfl

theorem familyTestSpace_bad (d : FiniteDistribution State) (N : ℕ) (δ : ℝ)
    (row : FiniteDistribution State) :
    @MeasurableSet (Finset (State → ℝ)) (familyTestSpace d N δ)
      {family | familyBadAt d N δ family row} := by
  apply MeasurableSpace.measurableSet_generateFrom
  exact Or.inr ⟨row, rfl⟩

/-- Direct random-family form: under the σ-algebra generated by the needed
family observations, independence from the actual empirical row gives the
paper's exact strict Hoeffding probability, for variable or empty families. -/
theorem randomFiniteFamily_empiricalRow_success_gt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (draw : Ω → Fin N → State) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure N)
    (family : Ω → Finset (State → ℝ))
    (hfamily : letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
      Measurable family)
    (hindep : letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ)
    (hV : ∀ᵐ ω ∂μ, ∀ V ∈ family ω, ∀ s, 0 ≤ V s) :
    1 - δ < μ.real {ω | ∀ V ∈ family ω,
      |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family ω).card / δ) / (2 * N))} := by
  letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
  apply d.randomFamily_empiricalRow_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw family hfamily id hindep hV
  · exact d.familyTestSpace_nonneg N δ
  · intro row _
    exact d.familyTestSpace_bad N δ row

/-- A finite-range variable has the same independence property when its
codomain is given the discrete σ-algebra, provided the original σ-algebra has
measurable singletons. -/
theorem indepFun_finiteRange_to_discrete
    {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSingletonClass R]
    (μ : Measure Ω) (f : Ω → Family) (g : Ω → R) (support : Finset R)
    (hrange : ∀ ω, g ω ∈ support) (hindep : IndepFun f g μ) :
    letI : MeasurableSpace R := ⊤
    IndepFun f g μ := by
  classical
  have hsmall : ∀ t : Set R, MeasurableSet ((support : Set R) ∩ t) := by
    intro t
    exact (support.finite_toSet.subset Set.inter_subset_left).measurableSet
  have hind := indepFun_iff_measure_inter_preimage_eq_mul.mp hindep
  letI : MeasurableSpace R := ⊤
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have ht' := hsmall t
  have hpre : g ⁻¹' ((support : Set R) ∩ t) = g ⁻¹' t := by
    ext ω
    simp [hrange ω]
  have h := hind s ((support : Set R) ∩ t) hs ht'
  simpa only [hpre] using h

/-- The empirical-row measurable structure inherited from the usual real
coordinate vector. -/
def rowVectorSpace : MeasurableSpace (FiniteDistribution State) :=
  MeasurableSpace.comap (fun row : FiniteDistribution State ↦ row.prob) inferInstance

/-- Every transition-row singleton is measurable in its coordinate σ-algebra. -/
theorem rowVectorSpace_singletons :
    @MeasurableSingletonClass (FiniteDistribution State) (rowVectorSpace (State := State)) := by
  letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
  refine ⟨?_⟩
  intro row
  have hm : Measurable[rowVectorSpace (State := State)]
      (fun r : FiniteDistribution State ↦ r.prob) := comap_measurable _
  have heq : (fun r : FiniteDistribution State ↦ r.prob) ⁻¹' {row.prob} = {row} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      cases r with
      | mk rp rn rs =>
        cases row with
        | mk qp qn qs =>
          simp only at h
          cases h
          rfl
    · intro h
      rw [h]
  rw [← heq]
  exact hm (measurableSet_singleton _)

/-- The direct source-shaped statement remains valid when independence of the
random family and empirical row is understood using the ordinary measurable
structure on the row's real coordinate vector. -/
theorem randomFiniteFamily_empiricalRow_success_gt_vectorSigma
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (draw : Ω → Fin N → State) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure N)
    (family : Ω → Finset (State → ℝ))
    (hfamily : letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
      Measurable family)
    (hindep : letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
      letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ)
    (hV : ∀ᵐ ω ∂μ, ∀ V ∈ family ω, ∀ s, 0 ≤ V s) :
    1 - δ < μ.real {ω | ∀ V ∈ family ω,
      |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
        Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family ω).card / δ) / (2 * N))} := by
  have hdiscrete : letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
      letI : MeasurableSpace (FiniteDistribution State) := ⊤
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ := by
    letI : MeasurableSpace (Finset (State → ℝ)) := familyTestSpace d N δ
    letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
    letI : MeasurableSingletonClass (FiniteDistribution State) := rowVectorSpace_singletons
    exact indepFun_finiteRange_to_discrete μ family
      (fun ω ↦ empiricalRow N hN (draw ω)) (empiricalRows N hN)
      (fun ω ↦ empiricalRow_mem_empiricalRows N hN (draw ω)) hindep
  exact d.randomFiniteFamily_empiricalRow_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw
    family hfamily hdiscrete hV

end Joint

end StatisticalRL.FiniteDistribution
