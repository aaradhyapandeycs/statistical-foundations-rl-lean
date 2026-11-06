import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Function

namespace StatisticalRL.PrelimFano

/-- Restricting an absolutely-continuous pair to a measurable cell preserves
the log-likelihood ratio almost everywhere on the restricted first law. -/
theorem llr_restrict_of_ac
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {s : Set Ω} (hs : MeasurableSet s) :
    MeasureTheory.llr (μ.restrict s) (ν.restrict s) =ᵐ[μ.restrict s]
      MeasureTheory.llr μ ν := by
  have hrepresentation : μ.restrict s =
      (ν.restrict s).withDensity (μ.rnDeriv ν) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hμν]
    rw [restrict_withDensity hs]
  have hdecomposition : μ.restrict s =
      0 + (ν.restrict s).withDensity (μ.rnDeriv ν) := by
    rw [zero_add, hrepresentation]
  have hderiv := Measure.eq_rnDeriv₀
    (μ := μ.restrict s) (ν := ν.restrict s)
    (f := μ.rnDeriv ν) (Measure.measurable_rnDeriv μ ν).aemeasurable
    Measure.MutuallySingular.zero_left hdecomposition
  have hderiv' : (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s]
      μ.rnDeriv ν := hderiv.symm
  have hderivμ : (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[μ.restrict s]
      μ.rnDeriv ν := (hμν.restrict s).ae_le hderiv'
  filter_upwards [hderivμ] with x hx
  simpa only [MeasureTheory.llr] using
    congrArg (fun r : ℝ≥0∞ => Real.log r.toReal) hx

/-- The restricted KL integral is the original log-likelihood integral over
the measurable cell, with the expected cell-mass correction. -/
theorem toReal_klDiv_restrict_of_ac
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hInt : Integrable (MeasureTheory.llr μ ν) μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (InformationTheory.klDiv (μ.restrict s) (ν.restrict s)).toReal =
      (∫ x in s, MeasureTheory.llr μ ν x ∂μ) + ν.real s - μ.real s := by
  have hllr := llr_restrict_of_ac μ ν hμν hs
  have hAC : μ.restrict s ≪ ν.restrict s := hμν.restrict s
  have hInt' : Integrable (MeasureTheory.llr (μ.restrict s) (ν.restrict s))
      (μ.restrict s) := hInt.restrict.congr hllr.symm
  rw [InformationTheory.toReal_klDiv hAC hInt']
  rw [MeasureTheory.integral_congr_ae hllr]
  simp only [MeasureTheory.measureReal_restrict_apply_univ]

/-- The restrictions of a measure to all fibers of a finite-valued measurable
map sum back to the original measure. -/
theorem sum_restrict_fibers
    {Ω Ξ : Type*} [MeasurableSpace Ω] [Fintype Ξ]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (μ : Measure Ω) (f : Ω → Ξ) (hf : Measurable f) :
    Measure.sum (fun y : Ξ ↦ μ.restrict (f ⁻¹' ({y} : Set Ξ))) = μ := by
  classical
  have hdis : Pairwise (Disjoint on fun y : Ξ ↦ f ⁻¹' ({y} : Set Ξ)) := by
    intro y z hyz
    show Disjoint (f ⁻¹' ({y} : Set Ξ)) (f ⁻¹' ({z} : Set Ξ))
    rw [Set.disjoint_left]
    intro x hx hz
    apply hyz
    have h1 : f x = y := by simpa using hx
    have h2 : f x = z := by simpa using hz
    exact h1.symm.trans h2
  have hmeas (y : Ξ) : MeasurableSet (f ⁻¹' ({y} : Set Ξ)) :=
    hf (measurableSet_singleton y)
  have hunion : (⋃ y : Ξ, f ⁻¹' ({y} : Set Ξ)) = Set.univ := by
    ext x
    simp
  calc
    Measure.sum (fun y : Ξ ↦ μ.restrict (f ⁻¹' ({y} : Set Ξ))) =
        μ.restrict (⋃ y : Ξ, f ⁻¹' ({y} : Set Ξ)) :=
      (Measure.restrict_iUnion hdis hmeas).symm
    _ = μ := by rw [hunion, Measure.restrict_univ]


end StatisticalRL.PrelimFano
