import Formalization.Probability.EmpiricalRow
import Mathlib.Probability.ConditionalExpectation

/-! A finite-product conditional law for a
past-measurable adaptive coordinate selected outside a fixed revealed block.
The random-revealed-set online coupling is not established in this module. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance onlineFreshOutcomeMeasurable : MeasurableSpace Outcome := ⊤
noncomputable local instance onlineFreshOutcomeDecidable : DecidableEq Outcome := Classical.decEq Outcome

noncomputable def onlineStackProductLaw (d : Index → FiniteDistribution Outcome) :
    Measure (Index → Outcome) := Measure.pi (fun i => (d i).rowMeasure)

instance onlineStackProductLaw_probability (d : Index → FiniteDistribution Outcome) :
    IsProbabilityMeasure (onlineStackProductLaw d) := by
  unfold onlineStackProductLaw
  infer_instance

def onlineRevealedCode (I : Finset Index) (data : Index → Outcome) : (i : I) → Outcome :=
  fun i => data i.val

noncomputable def onlineRevealedSigma (I : Finset Index) : MeasurableSpace (Index → Outcome) :=
  MeasurableSpace.comap (onlineRevealedCode I) inferInstance

/-- A fixed unrevealed coordinate is independent of the entire revealed block
under the actual finite product measure, derived from product independence. -/
theorem onlineUnrevealedCoordinate_indep_code
    (d : Index → FiniteDistribution Outcome) (I : Finset Index)
    (i : Index) (hi : i ∉ I) :
    IndepFun (onlineRevealedCode I) (fun data : Index → Outcome => data i)
      (onlineStackProductLaw d) := by
  classical
  have hind : iIndepFun (fun j (data : Index → Outcome) => data j)
      (onlineStackProductLaw d) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdis : Disjoint I {i} := by simpa using hi
  have hb := iIndepFun.indepFun_finset I {i} hdis hind (fun j => measurable_pi_apply j)
  let get : ((j : ({i} : Finset Index)) → Outcome) → Outcome :=
    fun code => code ⟨i,by simp⟩
  have h := hb.comp measurable_id (measurable_of_countable get)
  exact h

/-- A fresh coordinate's conditional singleton probability is its actual row
mass, including zero-mass outcomes. -/
theorem onlineUnrevealedIndicator_condExp
    (d : Index → FiniteDistribution Outcome) (I : Finset Index)
    (i : Index) (hi : i ∉ I) (x : Outcome) :
    (onlineStackProductLaw d)[(fun data => if data i=x then (1 : ℝ) else 0) |
      onlineRevealedSigma I] =ᵐ[onlineStackProductLaw d] fun _ => (d i).prob x := by
  classical
  let μ := onlineStackProductLaw d
  let fresh : MeasurableSpace (Index → Outcome) := MeasurableSpace.comap (fun data : Index → Outcome => data i)
    (inferInstance : MeasurableSpace Outcome)
  letI : MeasurableSpace (Index → Outcome) := MeasurableSpace.pi
  have hfresh : fresh ≤ (inferInstance : MeasurableSpace (Index → Outcome)) :=
    (measurable_pi_apply i : Measurable (fun data : Index → Outcome => data i)).comap_le
  have hpast : onlineRevealedSigma I ≤
      (inferInstance : MeasurableSpace (Index → Outcome)) :=
    (measurable_of_countable (onlineRevealedCode I)).comap_le
  have hind : Indep fresh (onlineRevealedSigma I) μ := by
    simpa [fresh, onlineRevealedSigma, IndepFun_iff_Indep] using
      (onlineUnrevealedCoordinate_indep_code d I i hi).symm
  let v : Outcome → ℝ := fun y => if y=x then 1 else 0
  have hv : StronglyMeasurable[fresh] (fun data : Index → Outcome => v (data i)) :=
    ((measurable_of_countable v).comp (comap_measurable _)).stronglyMeasurable
  have hc := condExp_indep_eq hfresh hpast hv hind
  have hmap : μ.map (fun data : Index → Outcome => data i) = (d i).rowMeasure :=
    (measurePreserving_eval (fun j => (d j).rowMeasure) i).map_eq
  have hint : (∫ data : Index → Outcome, v (data i) ∂μ) = (d i).prob x := by
    have h := integral_map (μ := μ) (measurable_pi_apply i).aemeasurable
      (Integrable.of_finite (f := v) (μ := μ.map (fun data => data i))).aestronglyMeasurable
    rw [hmap, FiniteDistribution.rowMeasure_integral] at h
    simpa [v, FiniteDistribution.expectation] using h.symm
  filter_upwards [hc] with data hd
  simpa [v, hint] using hd

end StatisticalRL.OnlineRL
