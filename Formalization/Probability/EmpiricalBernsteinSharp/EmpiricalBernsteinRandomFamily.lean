import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalBernsteinFiniteFamily
import Formalization.Probability.BernsteinFamily

/-! Private uncompiled Borel-family transfer for empirical Bernstein. -/
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance empiricalBernsteinRandomStateMeasurable : MeasurableSpace State := ⊤
local instance empiricalBernsteinRandomRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

noncomputable def empiricalBernsteinFamilyBadAt (d : FiniteDistribution State) (N : ℕ) (δ : ℝ)
    (family : Finset (State → ℝ)) (row : FiniteDistribution State) : Prop :=
  ∃ V ∈ family, empiricalBernsteinFamilyRadius row N family.card δ V < |row.expectation V - d.expectation V|

theorem empiricalRowLaw_empiricalBernsteinBad_lt (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (hN2 : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (family : Finset (State → ℝ)) (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    (d.empiricalRowLaw N hN).real {row | empiricalBernsteinFamilyBadAt d N δ family row} < δ := by
  classical
  unfold empiricalRowLaw
  rw [measureReal_def, Measure.map_apply (measurable_of_countable _)
    (by exact MeasurableSpace.measurableSet_top)]
  change (d.sampleMeasure N).real {ω | empiricalBernsteinFamilyBadAt d N δ family (empiricalRow N hN ω)} < δ
  have hs := d.empiricalBernstein_fixedFamily_success_gt N hN2 family δ hδ hδ1 hV
  let good : Set (Fin N → State) := {ω | ∀ V ∈ family,
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤ empiricalBernsteinFamilyRadius (empiricalRow N hN ω) N family.card δ V}
  have hg : MeasurableSet good := (Set.to_countable good).measurableSet
  have heq : {ω | empiricalBernsteinFamilyBadAt d N δ family (empiricalRow N hN ω)} = goodᶜ := by
    ext ω
    simp [empiricalBernsteinFamilyBadAt, good, not_le]
  rw [heq, measureReal_compl hg, probReal_univ]
  linarith

section Joint

variable {Family : Type*} [MeasurableSpace Family]

/-- The measurable failure set on a family code and an attainable empirical row. -/
noncomputable def supportedEmpiricalBernsteinBad (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ)) :
    Set (Family × FiniteDistribution State) :=
  ⋃ row ∈ empiricalRows N hN, {c | empiricalBernsteinFamilyBadAt d N δ (family c) row} ×ˢ {row}

theorem measurableSet_supportedEmpiricalBernsteinBad (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ))
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | empiricalBernsteinFamilyBadAt d N δ (family c) row}) :
    MeasurableSet (supportedEmpiricalBernsteinBad d N hN δ family) := by
  classical
  apply Finset.measurableSet_biUnion
  intro row hrow
  exact (hbad row hrow).prod (measurableSet_singleton row)

omit [MeasurableSpace Family] in
@[simp] theorem mem_supportedEmpiricalBernsteinBad_empirical (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ))
    (c : Family) (ω : Fin N → State) :
    (c, empiricalRow N hN ω) ∈ supportedEmpiricalBernsteinBad d N hN δ family ↔
      empiricalBernsteinFamilyBadAt d N δ (family c) (empiricalRow N hN ω) := by
  classical
  simp [supportedEmpiricalBernsteinBad, empiricalRow_mem_empiricalRows]

/-- Mixing independent empirical rows with arbitrary (possibly continuously
varying) family codes preserves strict failure probability below δ. -/
theorem product_supportedEmpiricalBernsteinBad_lt (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (hN2 : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ν : Measure Family) [IsProbabilityMeasure ν]
    (family : Family → Finset (State → ℝ))
    (hV : ∀ᵐ c ∂ν, ∀ V ∈ family c, ∀ s, 0 ≤ V s)
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | empiricalBernsteinFamilyBadAt d N δ (family c) row}) :
    ν.prod (d.empiricalRowLaw N hN) (supportedEmpiricalBernsteinBad d N hN δ family) < ENNReal.ofReal δ := by
  classical
  let ρ := d.empiricalRowLaw N hN
  let bad := supportedEmpiricalBernsteinBad d N hN δ family
  have hm : MeasurableSet bad := measurableSet_supportedEmpiricalBernsteinBad d N hN δ family hbad
  have hsec (c : Family) : ρ {r | (c, r) ∈ bad} =
      ρ {r | empiricalBernsteinFamilyBadAt d N δ (family c) r} := by
    dsimp only [ρ, empiricalRowLaw]
    rw [Measure.map_apply (measurable_of_countable _) (by exact MeasurableSpace.measurableSet_top),
      Measure.map_apply (measurable_of_countable _) (by exact MeasurableSpace.measurableSet_top)]
    congr 1
    ext ω
    exact mem_supportedEmpiricalBernsteinBad_empirical d N hN δ family c ω
  have hpoint : ∀ᵐ c ∂ν, ρ {r | (c, r) ∈ bad} < ENNReal.ofReal δ := by
    filter_upwards [hV] with c hc
    rw [hsec]
    have hb := d.empiricalRowLaw_empiricalBernsteinBad_lt N hN hN2 δ hδ hδ1 (family c) hc
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
be independent of the ordered sample), satisfies the strict Bernstein bound.
The family code may have an arbitrary measurable type and variable cardinality. -/
theorem randomFamily_empiricalBernstein_success_gt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (draw : Ω → Fin N → State) (hdraw : Measurable draw)
    (hlaw : μ.map draw = d.sampleMeasure N)
    (code : Ω → Family) (hcode : Measurable code)
    (family : Family → Finset (State → ℝ))
    (hindep : IndepFun code (fun ω ↦ empiricalRow N hN (draw ω)) μ)
    (hV : ∀ᵐ ω ∂μ, ∀ V ∈ family (code ω), ∀ s, 0 ≤ V s)
    (hVmeas : MeasurableSet {c | ∀ V ∈ family c, ∀ s, 0 ≤ V s})
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | empiricalBernsteinFamilyBadAt d N δ (family c) row}) :
    1 - δ < μ.real {ω | ∀ V ∈ family (code ω),
      |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
        empiricalBernsteinFamilyRadius (empiricalRow N hN (draw ω)) N (family (code ω)).card δ V} := by
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
  let bad := supportedEmpiricalBernsteinBad d N hN δ family
  have hm : MeasurableSet bad := measurableSet_supportedEmpiricalBernsteinBad d N hN δ family hbad
  have hpair : Measurable (fun ω ↦ (code ω, row ω)) := hcode.prodMk hrow
  have hindmap := (indepFun_iff_map_prod_eq_prod_map_map hcode.aemeasurable hrow.aemeasurable).mp hindep
  have hprob : μ ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) < ENNReal.ofReal δ := by
    rw [← Measure.map_apply hpair hm, hindmap, hrowlaw]
    exact d.product_supportedEmpiricalBernsteinBad_lt N hN hN2 δ hδ hδ1 ν family hVν hbad
  have hreal : μ.real ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hprob
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using h
  have hmeas : MeasurableSet ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) := hm.preimage hpair
  have heq : ((fun ω ↦ (code ω, row ω)) ⁻¹' bad)ᶜ =
      {ω | ∀ V ∈ family (code ω),
        |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
          empiricalBernsteinFamilyRadius (empiricalRow N hN (draw ω)) N (family (code ω)).card δ V} := by
    ext ω
    simp [bad, row, empiricalBernsteinFamilyBadAt, not_lt]
  have hc := measureReal_compl (μ := μ) hmeas
  rw [heq, probReal_univ] at hc
  exact (sub_lt_sub_left hreal 1).trans_eq hc.symm

end Joint

theorem randomBorelFamily_empiricalBernstein_success_gt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
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
        empiricalBernsteinFamilyRadius (empiricalRow N hN (draw ω)) N (family ω).card δ V} := by
  letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
  have hdiscrete : letI : MeasurableSpace (FiniteDistribution State) := ⊤
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ := by
    letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
    letI : MeasurableSingletonClass (FiniteDistribution State) := rowVectorSpace_singletons
    exact indepFun_finiteRange_to_discrete μ family
      (fun ω ↦ empiricalRow N hN (draw ω)) (empiricalRows N hN)
      (fun ω ↦ empiricalRow_mem_empiricalRows N hN (draw ω)) hindep
  apply d.randomFamily_empiricalBernstein_success_gt μ N hN hN2 δ hδ hδ1 draw hdraw hlaw
    family hfamily id hdiscrete hV
  · apply (finiteFamilyBorel_measurableSet_iff _).2
    intro n
    exact enumerationFamily_nonneg_measurable n
  · intro row _
    exact empiricalBernsteinFamily_violation_measurable d row N δ


end StatisticalRL.FiniteDistribution
