import Formalization.Probability.SharpEmpiricalBernstein
import Formalization.Probability.RandomFamilyBorel

/-! Simultaneous Bernstein inequalities for independent finite vector families. -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance bernsteinFamilyStateMeasurable : MeasurableSpace State := ⊤
local instance bernsteinFamilyRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

noncomputable def bernsteinRadius (d : FiniteDistribution State) (N k : ℕ) (δ : ℝ)
    (V : State → ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (4 * k / δ) * d.variance V / N) +
    2 * ‖V‖ * Real.log (4 * k / δ) / (3 * N)

/-- The square-root term is exactly the source's product form. -/
theorem bernsteinRadius_eq_source (d : FiniteDistribution State) (N k : ℕ) (δ : ℝ)
    (V : State → ℝ) :
    bernsteinRadius d N k δ V =
      Real.sqrt (2 * Real.log (4 * k / δ) / N) * Real.sqrt (d.variance V) +
      2 * ‖V‖ * Real.log (4 * k / δ) / (3 * N) := by
  unfold bernsteinRadius
  have h : 2 * Real.log (4 * (k : ℝ) / δ) * d.variance V / N =
      (2 * Real.log (4 * (k : ℝ) / δ) / N) * d.variance V := by ring
  rw [h, Real.sqrt_mul' _ (d.variance_nonneg V)]

noncomputable def bernsteinViolation (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (k : ℕ) (δ : ℝ) (V : State → ℝ) : Set (Fin N → State) :=
  {ω | bernsteinRadius d N k δ V < |(empiricalRow N hN ω).expectation V - d.expectation V|}

/-- The factor 4 in the source logarithm yields failure at most δ/(2k). -/
theorem bernsteinViolation_le (d : FiniteDistribution State) (N k : ℕ) (hN : 0 < N)
    (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (V : State → ℝ) (hV : ∀ s, 0 ≤ V s) :
    (d.sampleMeasure N).real (d.bernsteinViolation N hN k δ V) ≤ δ / (2 * k) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 1 < 4 * (k : ℝ) / δ := by
    apply (lt_div_iff₀ hδ).2
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hl : 0 < Real.log (4 * (k : ℝ) / δ) := Real.log_pos hx
  have hupper (s : State) : V s ∈ Set.Icc 0 ‖V‖ := by
    refine ⟨hV s, ?_⟩
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)
  have h := d.empiricalRow_source_threshold_strict V N hN ‖V‖
    (Real.log (4 * k / δ)) (norm_nonneg _) hl hupper
  calc
    _ ≤ 2 * Real.exp (-Real.log (4 * (k : ℝ) / δ)) := h
    _ = δ / (2 * k) := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (k : ℝ) / δ)]
      field_simp
      norm_num

/-- Strict source success, including an empty family and zero variances. -/
theorem empiricalRow_bernsteinFamily_success_gt (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (family : Finset (State → ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    1 - δ < (d.sampleMeasure N).real
      {ω | ∀ V ∈ family,
        |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
          bernsteinRadius d N family.card δ V} := by
  classical
  by_cases hne : family.Nonempty
  · let bad : Set (Fin N → State) := ⋃ V ∈ family, d.bernsteinViolation N hN family.card δ V
    have hk : 0 < family.card := Finset.card_pos.mpr hne
    have hkr : (0 : ℝ) < family.card := by exact_mod_cast hk
    have hb : (d.sampleMeasure N).real bad ≤ δ / 2 := by
      calc
        _ ≤ ∑ V ∈ family, (d.sampleMeasure N).real
            (d.bernsteinViolation N hN family.card δ V) := measureReal_biUnion_finset_le _ _
        _ ≤ ∑ _V ∈ family, δ / (2 * family.card) := Finset.sum_le_sum (fun V h ↦
          d.bernsteinViolation_le N family.card hN hk δ hδ hδ1 V (hV V h))
        _ = δ / 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          field_simp
    have hm : MeasurableSet bad := (Set.to_countable bad).measurableSet
    have heq : badᶜ = {ω | ∀ V ∈ family,
        |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
          bernsteinRadius d N family.card δ V} := by
      ext ω
      simp [bad, bernsteinViolation, not_lt]
    have hc := measureReal_compl (μ := d.sampleMeasure N) hm
    rw [heq, probReal_univ] at hc
    linarith
  · have hzero : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst family
    simp [probReal_univ, hδ]


noncomputable def bernsteinFamilyBadAt (d : FiniteDistribution State) (N : ℕ) (δ : ℝ)
    (family : Finset (State → ℝ)) (row : FiniteDistribution State) : Prop :=
  ∃ V ∈ family, bernsteinRadius d N family.card δ V < |row.expectation V - d.expectation V|

theorem empiricalRowLaw_bernsteinBad_lt (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (family : Finset (State → ℝ)) (hV : ∀ V ∈ family, ∀ s, 0 ≤ V s) :
    (d.empiricalRowLaw N hN).real {row | bernsteinFamilyBadAt d N δ family row} < δ := by
  classical
  unfold empiricalRowLaw
  rw [measureReal_def, Measure.map_apply (measurable_of_countable _)
    (by exact MeasurableSpace.measurableSet_top)]
  change (d.sampleMeasure N).real {ω | bernsteinFamilyBadAt d N δ family (empiricalRow N hN ω)} < δ
  have hs := d.empiricalRow_bernsteinFamily_success_gt N hN family δ hδ hδ1 hV
  let good : Set (Fin N → State) := {ω | ∀ V ∈ family,
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤ bernsteinRadius d N family.card δ V}
  have hg : MeasurableSet good := (Set.to_countable good).measurableSet
  have heq : {ω | bernsteinFamilyBadAt d N δ family (empiricalRow N hN ω)} = goodᶜ := by
    ext ω
    simp [bernsteinFamilyBadAt, good, not_le]
  rw [heq, measureReal_compl hg, probReal_univ]
  linarith

section Joint

variable {Family : Type*} [MeasurableSpace Family]

/-- The measurable failure set on a family code and an attainable empirical row. -/
noncomputable def supportedBernsteinBad (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ)) :
    Set (Family × FiniteDistribution State) :=
  ⋃ row ∈ empiricalRows N hN, {c | bernsteinFamilyBadAt d N δ (family c) row} ×ˢ {row}

theorem measurableSet_supportedBernsteinBad (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ))
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | bernsteinFamilyBadAt d N δ (family c) row}) :
    MeasurableSet (supportedBernsteinBad d N hN δ family) := by
  classical
  apply Finset.measurableSet_biUnion
  intro row hrow
  exact (hbad row hrow).prod (measurableSet_singleton row)

omit [MeasurableSpace Family] in
@[simp] theorem mem_supportedBernsteinBad_empirical (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (family : Family → Finset (State → ℝ))
    (c : Family) (ω : Fin N → State) :
    (c, empiricalRow N hN ω) ∈ supportedBernsteinBad d N hN δ family ↔
      bernsteinFamilyBadAt d N δ (family c) (empiricalRow N hN ω) := by
  classical
  simp [supportedBernsteinBad, empiricalRow_mem_empiricalRows]

/-- Mixing independent empirical rows with arbitrary (possibly continuously
varying) family codes preserves strict failure probability below δ. -/
theorem product_supportedBernsteinBad_lt (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ν : Measure Family) [IsProbabilityMeasure ν]
    (family : Family → Finset (State → ℝ))
    (hV : ∀ᵐ c ∂ν, ∀ V ∈ family c, ∀ s, 0 ≤ V s)
    (hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c | bernsteinFamilyBadAt d N δ (family c) row}) :
    ν.prod (d.empiricalRowLaw N hN) (supportedBernsteinBad d N hN δ family) < ENNReal.ofReal δ := by
  classical
  let ρ := d.empiricalRowLaw N hN
  let bad := supportedBernsteinBad d N hN δ family
  have hm : MeasurableSet bad := measurableSet_supportedBernsteinBad d N hN δ family hbad
  have hsec (c : Family) : ρ {r | (c, r) ∈ bad} =
      ρ {r | bernsteinFamilyBadAt d N δ (family c) r} := by
    dsimp only [ρ, empiricalRowLaw]
    rw [Measure.map_apply (measurable_of_countable _) (by exact MeasurableSpace.measurableSet_top),
      Measure.map_apply (measurable_of_countable _) (by exact MeasurableSpace.measurableSet_top)]
    congr 1
    ext ω
    exact mem_supportedBernsteinBad_empirical d N hN δ family c ω
  have hpoint : ∀ᵐ c ∂ν, ρ {r | (c, r) ∈ bad} < ENNReal.ofReal δ := by
    filter_upwards [hV] with c hc
    rw [hsec]
    have hb := d.empiricalRowLaw_bernsteinBad_lt N hN δ hδ hδ1 (family c) hc
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
theorem randomFamily_bernstein_success_gt
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
      MeasurableSet {c | bernsteinFamilyBadAt d N δ (family c) row}) :
    1 - δ < μ.real {ω | ∀ V ∈ family (code ω),
      |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
        bernsteinRadius d N (family (code ω)).card δ V} := by
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
  let bad := supportedBernsteinBad d N hN δ family
  have hm : MeasurableSet bad := measurableSet_supportedBernsteinBad d N hN δ family hbad
  have hpair : Measurable (fun ω ↦ (code ω, row ω)) := hcode.prodMk hrow
  have hindmap := (indepFun_iff_map_prod_eq_prod_map_map hcode.aemeasurable hrow.aemeasurable).mp hindep
  have hprob : μ ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) < ENNReal.ofReal δ := by
    rw [← Measure.map_apply hpair hm, hindmap, hrowlaw]
    exact d.product_supportedBernsteinBad_lt N hN δ hδ hδ1 ν family hVν hbad
  have hreal : μ.real ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hprob
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using h
  have hmeas : MeasurableSet ((fun ω ↦ (code ω, row ω)) ⁻¹' bad) := hm.preimage hpair
  have heq : ((fun ω ↦ (code ω, row ω)) ⁻¹' bad)ᶜ =
      {ω | ∀ V ∈ family (code ω),
        |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
          bernsteinRadius d N (family (code ω)).card δ V} := by
    ext ω
    simp [bad, row, bernsteinFamilyBadAt, not_lt]
  have hc := measureReal_compl (μ := μ) hmeas
  rw [heq, probReal_univ] at hc
  exact (sub_lt_sub_left hreal 1).trans_eq hc.symm

end Joint

/-- Every Bernstein test is measurable on each finite Borel enumeration. -/
theorem enumerationFamily_bernsteinBad_measurable (d : FiniteDistribution State)
    (N : ℕ) (δ : ℝ) (row : FiniteDistribution State) (n : ℕ) :
    MeasurableSet {v : FamilyEnumeration (State := State) n |
      bernsteinFamilyBadAt d N δ (enumerationFamily n v) row} := by
  classical
  have heq : {v : FamilyEnumeration (State := State) n |
      bernsteinFamilyBadAt d N δ (enumerationFamily n v) row} =
      ⋃ i : Fin n, {v | bernsteinRadius d N n δ (v.1 i) <
        |row.expectation (v.1 i) - d.expectation (v.1 i)|} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, bernsteinFamilyBadAt, enumerationFamily_card]
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
  have hsq : Measurable (fun v : FamilyEnumeration (State := State) n ↦
      d.expectation (fun s ↦ (v.1 i s) ^ 2)) := by
    unfold FiniteDistribution.expectation
    exact Finset.measurable_sum _ (fun s _ ↦
      measurable_const.mul (((measurable_pi_apply s).comp hv).pow_const 2))
  have hvar : Measurable (fun v : FamilyEnumeration (State := State) n ↦ d.variance (v.1 i)) := by
    simpa only [FiniteDistribution.variance] using hsq.sub ((heval d).pow_const 2)
  unfold bernsteinRadius
  have hr : Measurable (fun v : FamilyEnumeration (State := State) n ↦
      Real.sqrt (2 * Real.log (4 * (n : ℝ) / δ) * d.variance (v.1 i) / N)) := by
    exact ((measurable_const.mul hvar).div_const (N : ℝ)).sqrt
  have hr' : Measurable (fun v : FamilyEnumeration (State := State) n ↦
      2 * ‖v.1 i‖ * Real.log (4 * (n : ℝ) / δ) / (3 * N)) := by
    exact ((measurable_const.mul hv.norm).mul_const _).div_const _
  exact measurableSet_lt (hr.add hr') ((heval row).sub (heval d)).abs

/-- Exact source probability for Borel unordered random families independent of the empirical row. -/
theorem randomBorelFamily_bernstein_success_gt
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
        bernsteinRadius d N (family ω).card δ V} := by
  letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
  have hdiscrete : letI : MeasurableSpace (FiniteDistribution State) := ⊤
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ := by
    letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
    letI : MeasurableSingletonClass (FiniteDistribution State) := rowVectorSpace_singletons
    exact indepFun_finiteRange_to_discrete μ family
      (fun ω ↦ empiricalRow N hN (draw ω)) (empiricalRows N hN)
      (fun ω ↦ empiricalRow_mem_empiricalRows N hN (draw ω)) hindep
  apply d.randomFamily_bernstein_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw
    family hfamily id hdiscrete hV
  · apply (finiteFamilyBorel_measurableSet_iff _).2
    intro n
    exact enumerationFamily_nonneg_measurable n
  · intro row _
    apply (finiteFamilyBorel_measurableSet_iff _).2
    intro n
    exact enumerationFamily_bernsteinBad_measurable d N δ row n

/-- Lemma 2.5's single-row Bernstein radius in its literal product form. -/
theorem randomBorelFamily_bernstein_source
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
        Real.sqrt (2 * Real.log (4 * (family ω).card / δ) / N) * Real.sqrt (d.variance V) +
        2 * ‖V‖ * Real.log (4 * (family ω).card / δ) / (3 * N)} := by
  simpa only [bernsteinRadius_eq_source] using
    d.randomBorelFamily_bernstein_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw family hfamily hindep hV

end StatisticalRL.FiniteDistribution
