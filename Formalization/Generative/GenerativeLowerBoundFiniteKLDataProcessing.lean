import Formalization.Generative.GenerativeLowerBoundFiniteDataProcessing
import Formalization.Generative.GenerativeLowerBoundKLAffinity

/-! Finite KL data-processing ingredients for actual finite laws. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StatisticalRL.GenerativeLowerBound

/-- A finite absolutely continuous pair admits the usual atomic KL expression,
including atoms of zero reference mass. -/
theorem finite_klDiv_eq_expression_of_ac {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    (InformationTheory.klDiv μ ν).toReal =
      finiteKLExpression (fun x ↦ μ.real {x}) (fun x ↦ ν.real {x}) := by
  have heq : μ Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac heq,
    integral_fintype _ Integrable.of_finite]
  unfold finiteKLExpression
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : ν {x} = 0
  · have hm : μ {x} = 0 := hac hz
    simp [measureReal_def, hm]
  · have hr : μ.rnDeriv ν x = μ {x} / ν {x} := by
      have h := Measure.setLIntegral_rnDeriv hac ({x} : Set Ω)
      rw [lintegral_singleton] at h
      apply (ENNReal.eq_div_iff hz (measure_ne_top ν _)).2
      simpa [mul_comm] using h
    rw [MeasureTheory.llr, hr, ENNReal.toReal_div]
    rfl

/-- Finite KL is finite under absolute continuity. -/
theorem finite_klDiv_ne_top_of_ac {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    InformationTheory.klDiv μ ν ≠ ∞ :=
  InformationTheory.klDiv_ne_top_iff.mpr ⟨hac, Integrable.of_finite⟩

/-- Deterministic coarse-graining decreases the atomic expression for positive
finite input masses, including decoder outputs with empty fibers. -/
theorem finite_expression_coarseGrain {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (a b : Ω → ℝ) (ha : ∀ x, 0 < a x) (hb : ∀ x, 0 < b x)
    (f : Ω → Ξ) :
    finiteKLExpression (fun y ↦ ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y), a x)
      (fun y ↦ ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y), b x) ≤
    finiteKLExpression a b := by
  classical
  unfold finiteKLExpression
  calc
    _ ≤ ∑ y : Ξ, ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y),
        a x * Real.log (a x / b x) := by
      apply Finset.sum_le_sum
      intro y _
      exact finite_cell_logSum _ a b (fun x _ ↦ ha x) (fun x _ ↦ hb x)
    _ = _ := by
      simpa using (Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f
        (fun x ↦ a x * Real.log (a x / b x)))

/-- Pushforward atom masses are the sums over the corresponding fibers. -/
theorem finite_map_real_singleton {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → Ξ) (y : Ξ) :
    (μ.map f).real {y} = ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y), μ.real {x} := by
  classical
  have hf : Measurable f := measurable_of_countable _
  rw [measureReal_def, Measure.map_apply hf (measurableSet_singleton _)]
  rw [← measureReal_def, sum_measureReal_singleton]
  congr 1
  ext x
  simp

/-- Finite KL data processing for arbitrary deterministic decoders of two
full-support finite probability laws. -/
theorem finite_klDiv_map_le {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, μ {x} ≠ 0) (hν : ∀ x, ν {x} ≠ 0) (f : Ω → Ξ) :
    (InformationTheory.klDiv (μ.map f) (ν.map f)).toReal ≤
      (InformationTheory.klDiv μ ν).toReal := by
  classical
  have hf : Measurable f := measurable_of_countable _
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hac := finite_fullSupport_ac μ ν hν
  have hmap : μ.map f ≪ ν.map f := by
    intro s hs
    rw [Measure.map_apply hf (Set.to_countable s).measurableSet] at hs ⊢
    exact hac hs
  rw [finite_klDiv_eq_expression_of_ac _ _ hmap,
    finite_klDiv_eq_expression_of_ac _ _ hac]
  simp_rw [finite_map_real_singleton]
  exact finite_expression_coarseGrain _ _
    (fun x ↦ ENNReal.toReal_pos (hμ x) (measure_ne_top μ _))
    (fun x ↦ ENNReal.toReal_pos (hν x) (measure_ne_top ν _)) f

end StatisticalRL.GenerativeLowerBound
