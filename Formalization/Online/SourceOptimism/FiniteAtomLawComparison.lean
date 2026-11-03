import Formalization.Probability.EmpiricalRow
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.ENNReal.BigOperators

/-! Finite atom normalization turns the proved
reset/path atom comparisons into equality on a common transcript carrier.
No support/coupling conclusion is assumed. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Data Atom Transcript : Type*} [Fintype Data] [Fintype Atom] [Countable Transcript]
variable [MeasurableSpace Data] [MeasurableSingletonClass Data]
variable [MeasurableSpace Transcript] [MeasurableSingletonClass Transcript]
local instance onlineAtomFiniteMeasurable : MeasurableSpace Atom := ⊤

/-- Distinct direct atoms have the correct stack masses; normalization forces
full stack mass onto their finite image and hence equality of transcript laws.
The atom masses are intermediate proved inputs, not desired whole-law premises. -/
theorem onlineFiniteAtom_law_comparison
    (μ : Measure Data) [IsProbabilityMeasure μ] (ν : FiniteDistribution Atom)
    (observe : Data → Transcript) (encode : Atom → Transcript)
    (hinj : Function.Injective encode)
    (hatom : ∀ a, μ {data | observe data=encode a}=ENNReal.ofReal (ν.prob a)) :
    (∀ᵐ data ∂μ, observe data ∈ Set.range encode) ∧
      μ.map observe=ν.rowMeasure.map encode := by
  classical
  let event : Atom → Set Data := fun a => {data | observe data=encode a}
  have hdis : Pairwise (fun a b => Disjoint (event a) (event b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro data ha hb
    exact hab (hinj (ha.symm.trans hb))
  have hmeas : ∀ a,MeasurableSet (event a) := fun _ => (Set.to_countable _).measurableSet
  have hmass : μ (⋃ a,event a)=1 := by
    rw [measure_iUnion hdis hmeas,tsum_fintype]
    simp only [event,hatom]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => ν.prob_nonneg a),ν.sum_prob]
    norm_num
  have hunion : (⋃ a,event a)={data | observe data∈Set.range encode} := by
    ext data
    simp only [Set.mem_iUnion,Set.mem_setOf_eq,Set.mem_range,event]
    constructor <;> rintro ⟨a,ha⟩ <;> exact ⟨a,ha.symm⟩
  have hnull : μ {data | observe data∉Set.range encode}=0 := by
    have hc := measure_compl (MeasurableSet.iUnion hmeas) (measure_ne_top μ _)
    rw [hmass,measure_univ] at hc
    rw [hunion] at hc
    simpa only [tsub_self] using hc
  have hsupport : ∀ᵐ data ∂μ, observe data∈Set.range encode := ae_iff.mpr hnull
  refine ⟨hsupport,?_⟩
  apply Measure.ext_of_singleton
  intro transcript
  rw [Measure.map_apply (measurable_of_countable observe) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable encode) (measurableSet_singleton _)]
  by_cases hmem : transcript∈Set.range encode
  · obtain ⟨a,rfl⟩ := hmem
    have hpre : encode ⁻¹' {encode a}={a} := by
      ext b
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      exact ⟨fun h => hinj h,fun h => congrArg encode h⟩
    rw [hpre,FiniteDistribution.rowMeasure,PMF.toMeasure_apply_singleton _ _
      (measurableSet_singleton _)]
    exact hatom a
  · have hpre : encode ⁻¹' {transcript}=∅ := by
      ext a
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
      intro ha
      exact hmem ⟨a,ha⟩
    rw [hpre,measure_empty]
    apply measure_mono_null _ hnull
    intro data hd
    change observe data∉Set.range encode
    have heq : observe data=transcript := hd
    simpa only [heq] using hmem


/-- The finite direct atom carrier itself is a common carrier after decoding.
The decoder can be arbitrary away from the derived full-mass encoded image. -/
theorem onlineFiniteAtom_decodedLaw [Nonempty Atom]
    (μ : Measure Data) [IsProbabilityMeasure μ] (ν : FiniteDistribution Atom)
    (observe : Data → Transcript) (encode : Atom → Transcript)
    (hinj : Function.Injective encode)
    (hatom : ∀ a, μ {data | observe data=encode a}=ENNReal.ofReal (ν.prob a)) :
    μ.map (fun data => Function.invFun encode (observe data))=ν.rowMeasure := by
  have hm := (onlineFiniteAtom_law_comparison μ ν observe encode hinj hatom).2
  have h := congrArg (fun law : Measure Transcript => law.map (Function.invFun encode)) hm
  dsimp only at h
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  have hid : Function.invFun encode ∘ encode = id :=
    funext (Function.leftInverse_invFun hinj)
  simpa only [hid,Measure.map_id] using h

end StatisticalRL.OnlineRL
