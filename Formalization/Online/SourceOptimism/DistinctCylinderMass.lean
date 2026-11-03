import Formalization.Online.SourceOptimism.FreshCoordinateSelection

/-! Finite cylinder factorization. Distinct fixed
coordinate labels may be the labels of one fixed adaptive history; no iid
claim conditional on a random visit count is used. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance onlineCylinderOutcomeMeasurable : MeasurableSpace Outcome := ⊤

/-- Exact mass of a finite transcript fixing distinct coordinates in the
actual finite product sample space, including zero-probability transcripts. -/
theorem onlineDistinctCylinder_mass
    (d : Index → FiniteDistribution Outcome) (n : ℕ)
    (label : Fin n → Index) (hinj : Function.Injective label)
    (value : Fin n → Outcome) :
    onlineStackProductLaw d {data | ∀ j, data (label j)=value j} =
      ∏ j, ENNReal.ofReal ((d (label j)).prob (value j)) := by
  classical
  let μ := onlineStackProductLaw d
  have hall : iIndepFun (fun i (data : Index → Outcome) => data i) μ :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hsel : iIndepFun (fun j (data : Index → Outcome) => data (label j)) μ :=
    hall.precomp hinj
  have hmass (i : Index) (x : Outcome) : μ {data | data i=x} =
      ENNReal.ofReal ((d i).prob x) := by
    have hmap : μ.map (fun data : Index → Outcome => data i)=(d i).rowMeasure :=
      (measurePreserving_eval (fun j => (d j).rowMeasure) i).map_eq
    change μ ((fun data : Index → Outcome => data i) ⁻¹' {x}) = _
    rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton x), hmap,
      FiniteDistribution.rowMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rfl
  have h := hsel.meas_iInter (s := fun j => {data : Index → Outcome | data (label j)=value j})
    (fun j => (comap_measurable (fun data : Index → Outcome => data (label j)))
      (measurableSet_singleton (value j)))
  have hevent : (⋂ j, {data : Index → Outcome | data (label j)=value j}) =
      {data | ∀ j, data (label j)=value j} := by ext data; simp
  rw [hevent] at h
  simpa only [hmass] using h

/-- In particular, appending a previously unread coordinate multiplies the
history cylinder mass by the true row mass. No conditional division is used. -/
theorem onlineDistinctCylinder_append_mass
    (d : Index → FiniteDistribution Outcome) (n : ℕ)
    (label : Fin (n+1) → Index) (hinj : Function.Injective label)
    (value : Fin (n+1) → Outcome) :
    onlineStackProductLaw d {data | ∀ j, data (label j)=value j} =
      (onlineStackProductLaw d {data | ∀ j : Fin n,
        data (label j.castSucc)=value j.castSucc}) *
      ENNReal.ofReal ((d (label (Fin.last n))).prob (value (Fin.last n))) := by
  have hprefix : Function.Injective (fun j : Fin n => label j.castSucc) :=
    hinj.comp (Fin.castSucc_injective n)
  rw [onlineDistinctCylinder_mass d (n+1) label hinj value,
    onlineDistinctCylinder_mass d n (fun j => label j.castSucc) hprefix
      (fun j => value j.castSucc)]
  exact Fin.prod_univ_castSucc _

end StatisticalRL.OnlineRL
