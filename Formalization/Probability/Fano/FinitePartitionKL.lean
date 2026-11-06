import Formalization.Probability.Fano.FiniteValuedMapDefinitions
import Formalization.Probability.Fano.FinitePartitionRestriction
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace StatisticalRL.PrelimFano

open StatisticalRL.GenerativeLowerBound

/-- Summing the restricted KL integrals over a finite measurable partition
recovers the full KL integral. The source pair need not have finite support. -/
theorem sum_restricted_toReal_klDiv_eq
    {Ω Ξ : Type*} [MeasurableSpace Ω] [Fintype Ξ]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hInt : Integrable (MeasureTheory.llr μ ν) μ)
    (f : Ω → Ξ) (hf : Measurable f) :
    (∑ y : Ξ, (InformationTheory.klDiv
      (μ.restrict (fiberOf f y)) (ν.restrict (fiberOf f y))).toReal) =
      (InformationTheory.klDiv μ ν).toReal := by
  classical
  let c : Ξ → Set Ω := fiberOf f
  have hsumμ : Measure.sum (fun y : Ξ ↦ μ.restrict (c y)) = μ := by
    simpa [c, fiberOf] using sum_restrict_fibers μ f hf
  have hIntSum : Integrable (MeasureTheory.llr μ ν)
      (Measure.sum (fun y : Ξ ↦ μ.restrict (c y))) := by
    rw [hsumμ]
    exact hInt
  have hIntegral :
      (∑ y : Ξ, ∫ x in c y, MeasureTheory.llr μ ν x ∂μ) =
        ∫ x, MeasureTheory.llr μ ν x ∂μ := by
    have h := MeasureTheory.integral_sum_measure hIntSum
    rw [hsumμ] at h
    rw [h, tsum_fintype]
  have hmassμ : (∑ y : Ξ, μ.real (c y)) = 1 := by
    have h := MeasureTheory.sum_measureReal_preimage_singleton
      (μ := μ) Finset.univ (fun y _ ↦ hf (measurableSet_singleton y))
    simpa [c, fiberOf, probReal_univ] using h
  have hmassν : (∑ y : Ξ, ν.real (c y)) = 1 := by
    have h := MeasureTheory.sum_measureReal_preimage_singleton
      (μ := ν) Finset.univ (fun y _ ↦ hf (measurableSet_singleton y))
    simpa [c, fiberOf, probReal_univ] using h
  have hcell (y : Ξ) :
      (InformationTheory.klDiv (μ.restrict (c y)) (ν.restrict (c y))).toReal =
        (∫ x in c y, MeasureTheory.llr μ ν x ∂μ) + ν.real (c y) - μ.real (c y) :=
    toReal_klDiv_restrict_of_ac μ ν hμν hInt (hf (measurableSet_singleton y))
  have hsumCell :
      (∑ y : Ξ, (InformationTheory.klDiv
        (μ.restrict (c y)) (ν.restrict (c y))).toReal) =
        (∫ x, MeasureTheory.llr μ ν x ∂μ) + ν.real Set.univ - μ.real Set.univ := by
    calc
      _ = (∑ y : Ξ, ∫ x in c y, MeasureTheory.llr μ ν x ∂μ) +
            (∑ y : Ξ, ν.real (c y)) - (∑ y : Ξ, μ.real (c y)) := by
          simp_rw [hcell]
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∫ x, MeasureTheory.llr μ ν x ∂μ) + ν.real Set.univ - μ.real Set.univ := by
          rw [hIntegral, hmassν, hmassμ]
          simp [MeasureTheory.probReal_univ]
  rw [InformationTheory.toReal_klDiv hμν hInt]
  exact hsumCell

/-- Deterministic finite-valued data processing for KL on an arbitrary source
probability space. -/
theorem finiteValued_klDiv_map_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [Fintype Ξ]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → Ξ) (hf : Measurable f) :
    InformationTheory.klDiv (μ.map f) (ν.map f) ≤ InformationTheory.klDiv μ ν := by
  classical
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  by_cases htop : InformationTheory.klDiv μ ν = ∞
  · rw [htop]
    exact le_top
  · have hfinite := InformationTheory.klDiv_ne_top_iff.mp htop
    rcases hfinite with ⟨hμν, hInt⟩
    have hmap : μ.map f ≪ ν.map f := hμν.map hf
    have hmapFinite : InformationTheory.klDiv (μ.map f) (ν.map f) ≠ ∞ :=
      finite_klDiv_ne_top_of_ac (μ.map f) (ν.map f) hmap
    have hreal :
        (InformationTheory.klDiv (μ.map f) (ν.map f)).toReal ≤
          (InformationTheory.klDiv μ ν).toReal := by
      rw [finite_klDiv_eq_expression_of_ac (μ.map f) (ν.map f) hmap]
      unfold finiteKLExpression
      have hcell (y : Ξ) :
          (μ.map f).real {y} = μ.real (fiberOf f y) := by
        rw [MeasureTheory.measureReal_def,
          Measure.map_apply hf (measurableSet_singleton y)]
        rfl
      have hcellν (y : Ξ) :
          (ν.map f).real {y} = ν.real (fiberOf f y) := by
        rw [MeasureTheory.measureReal_def,
          Measure.map_apply hf (measurableSet_singleton y)]
        rfl
      have hsumKL := sum_restricted_toReal_klDiv_eq μ ν hμν hInt f hf
      have hcellLower (y : Ξ) :
          μ.real (fiberOf f y) *
              Real.log (μ.real (fiberOf f y) / ν.real (fiberOf f y)) +
            ν.real (fiberOf f y) - μ.real (fiberOf f y) ≤
          (InformationTheory.klDiv
            (μ.restrict (fiberOf f y)) (ν.restrict (fiberOf f y))).toReal := by
        have hACy : μ.restrict (fiberOf f y) ≪ ν.restrict (fiberOf f y) :=
          hμν.restrict (fiberOf f y)
        have hInty : Integrable
            (MeasureTheory.llr (μ.restrict (fiberOf f y))
              (ν.restrict (fiberOf f y))) (μ.restrict (fiberOf f y)) :=
          hInt.restrict.congr
            (llr_restrict_of_ac μ ν hμν (hf (measurableSet_singleton y))).symm
        simpa only [MeasureTheory.measureReal_restrict_apply_univ] using
          InformationTheory.mul_log_le_toReal_klDiv hACy hInty
      have hsumLower := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) ↦ hcellLower y)
      have hmassμ : (∑ y : Ξ, μ.real (fiberOf f y)) = 1 := by
        simpa [fiberOf, probReal_univ] using
          (MeasureTheory.sum_measureReal_preimage_singleton
            (μ := μ) Finset.univ (fun y _ ↦ hf (measurableSet_singleton y)))
      have hmassν : (∑ y : Ξ, ν.real (fiberOf f y)) = 1 := by
        simpa [fiberOf, probReal_univ] using
          (MeasureTheory.sum_measureReal_preimage_singleton
            (μ := ν) Finset.univ (fun y _ ↦ hf (measurableSet_singleton y)))
      have hsumTerms :
          (∑ y : Ξ, (μ.map f).real {y} *
            Real.log ((μ.map f).real {y} / (ν.map f).real {y})) =
          ∑ y : Ξ, (μ.real (fiberOf f y) *
            Real.log (μ.real (fiberOf f y) / ν.real (fiberOf f y))) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hcell, hcellν]
      rw [hsumTerms]
      have hcancel :
          (∑ y : Ξ, (μ.real (fiberOf f y) *
              Real.log (μ.real (fiberOf f y) / ν.real (fiberOf f y)) +
            ν.real (fiberOf f y) - μ.real (fiberOf f y))) =
            ∑ y : Ξ, μ.real (fiberOf f y) *
              Real.log (μ.real (fiberOf f y) / ν.real (fiberOf f y)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hmassν, hmassμ]
        simp
      calc
        _ = ∑ y : Ξ, (μ.real (fiberOf f y) *
              Real.log (μ.real (fiberOf f y) / ν.real (fiberOf f y)) +
            ν.real (fiberOf f y) - μ.real (fiberOf f y)) := hcancel.symm
        _ ≤ ∑ y : Ξ, (InformationTheory.klDiv
              (μ.restrict (fiberOf f y)) (ν.restrict (fiberOf f y))).toReal := hsumLower
        _ = (InformationTheory.klDiv μ ν).toReal := hsumKL
    exact (ENNReal.toReal_le_toReal hmapFinite htop).mp hreal


end StatisticalRL.PrelimFano
