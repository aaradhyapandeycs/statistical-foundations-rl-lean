import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Formalization.PrelimKL.KLBinaryProductRNDerivative
import Mathlib.MeasureTheory.Integral.Prod

/-! Finite-KL branch of the binary-product identity for `lem:KL-tensorize`
(`chapters/prelim.tex:1313–1319`). -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.PrelimKL

/-- KL additivity for two probability products when both coordinate divergences are finite. -/
theorem binary_product_toReal_klDiv_of_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (h₁ : InformationTheory.klDiv P₁ Q₁ ≠ ∞)
    (h₂ : InformationTheory.klDiv P₂ Q₂ ≠ ∞) :
    (InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂)).toReal =
      (InformationTheory.klDiv P₁ Q₁).toReal +
      (InformationTheory.klDiv P₂ Q₂).toReal := by
  let f := P₁.rnDeriv Q₁
  let g := P₂.rnDeriv Q₂
  have h₁ac : P₁ ≪ Q₁ := (InformationTheory.klDiv_ne_top_iff.mp h₁).1
  have h₂ac : P₂ ≪ Q₂ := (InformationTheory.klDiv_ne_top_iff.mp h₂).1
  have h₁int : Integrable (MeasureTheory.llr P₁ Q₁) P₁ :=
    (InformationTheory.klDiv_ne_top_iff.mp h₁).2
  have h₂int : Integrable (MeasureTheory.llr P₂ Q₂) P₂ :=
    (InformationTheory.klDiv_ne_top_iff.mp h₂).2
  have hprodac : P₁.prod P₂ ≪ Q₁.prod Q₂ := h₁ac.prod h₂ac
  have hRN : (P₁.prod P₂).rnDeriv (Q₁.prod Q₂) =ᵐ[Q₁.prod Q₂]
      fun z : α × β ↦ f z.1 * g z.2 := by
    simpa [f, g] using rnDeriv_prod_eq_mul_ae P₁ Q₁ P₂ Q₂ h₁ac h₂ac
  have hRNprod : (P₁.prod P₂).rnDeriv (Q₁.prod Q₂) =ᵐ[P₁.prod P₂]
      fun z : α × β ↦ f z.1 * g z.2 := hprodac.ae_le hRN
  have h₁pos : ∀ᵐ x ∂P₁, 0 < f x := by
    simpa [f] using Measure.rnDeriv_pos h₁ac
  have h₂pos : ∀ᵐ y ∂P₂, 0 < g y := by
    simpa [g] using Measure.rnDeriv_pos h₂ac
  have h₁finiteQ : ∀ᵐ x ∂Q₁, f x < ∞ := by
    simpa [f] using Measure.rnDeriv_lt_top P₁ Q₁
  have h₂finiteQ : ∀ᵐ y ∂Q₂, g y < ∞ := by
    simpa [g] using Measure.rnDeriv_lt_top P₂ Q₂
  have h₁finite : ∀ᵐ x ∂P₁, f x < ∞ := h₁ac.ae_le h₁finiteQ
  have h₂finite : ∀ᵐ y ∂P₂, g y < ∞ := h₂ac.ae_le h₂finiteQ
  have hfstMap : Measure.map Prod.fst (P₁.prod P₂) = P₁ :=
    (measurePreserving_fst (μ := P₁) (ν := P₂)).map_eq
  have hsndMap : Measure.map Prod.snd (P₁.prod P₂) = P₂ :=
    (measurePreserving_snd (μ := P₁) (ν := P₂)).map_eq
  have h₁posMapped : ∀ᵐ x ∂Measure.map Prod.fst (P₁.prod P₂), 0 < f x := by
    simpa [hfstMap] using h₁pos
  have h₂posMapped : ∀ᵐ y ∂Measure.map Prod.snd (P₁.prod P₂), 0 < g y := by
    simpa [hsndMap] using h₂pos
  have h₁finiteMapped : ∀ᵐ x ∂Measure.map Prod.fst (P₁.prod P₂), f x < ∞ := by
    simpa [hfstMap] using h₁finite
  have h₂finiteMapped : ∀ᵐ y ∂Measure.map Prod.snd (P₁.prod P₂), g y < ∞ := by
    simpa [hsndMap] using h₂finite
  have h₁posProd : ∀ᵐ z ∂P₁.prod P₂, 0 < f z.1 :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_const (Measure.measurable_rnDeriv P₁ Q₁))).mp h₁posMapped
  have h₂posProd : ∀ᵐ z ∂P₁.prod P₂, 0 < g z.2 :=
    (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt measurable_const (Measure.measurable_rnDeriv P₂ Q₂))).mp h₂posMapped
  have h₁finiteProd : ∀ᵐ z ∂P₁.prod P₂, f z.1 < ∞ :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv P₁ Q₁) measurable_const)).mp h₁finiteMapped
  have h₂finiteProd : ∀ᵐ z ∂P₁.prod P₂, g z.2 < ∞ :=
    (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv P₂ Q₂) measurable_const)).mp h₂finiteMapped
  have hllr : MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂) =ᵐ[P₁.prod P₂]
      fun z : α × β ↦ MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2 := by
    filter_upwards [hRNprod, h₁posProd, h₂posProd, h₁finiteProd, h₂finiteProd]
      with z hderiv h₁p h₂p h₁lt h₂lt
    simp only [MeasureTheory.llr] at hderiv ⊢
    rw [hderiv, ENNReal.toReal_mul,
      Real.log_mul (ENNReal.toReal_pos h₁p.ne' h₁lt.ne).ne'
        (ENNReal.toReal_pos h₂p.ne' h₂lt.ne).ne']
  have hsumInt : Integrable
      (fun z : α × β ↦ MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2)
      (P₁.prod P₂) :=
    (h₁int.comp_fst P₂).add (h₂int.comp_snd P₁)
  have hprodInt : Integrable (MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂))
      (P₁.prod P₂) := (integrable_congr hllr).2 hsumInt
  have hmass : (P₁.prod P₂) Set.univ = (Q₁.prod Q₂) Set.univ := by
    simp [measure_univ]
  have hmass₁ : P₁ Set.univ = Q₁ Set.univ := by simp [measure_univ]
  have hmass₂ : P₂ Set.univ = Q₂ Set.univ := by simp [measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hprodac hmass,
    InformationTheory.toReal_klDiv_of_measure_eq h₁ac hmass₁,
    InformationTheory.toReal_klDiv_of_measure_eq h₂ac hmass₂]
  calc
    ∫ z, MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂) z ∂P₁.prod P₂
        = ∫ z, MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2 ∂P₁.prod P₂ :=
          integral_congr_ae hllr
    _ = (∫ z, MeasureTheory.llr P₁ Q₁ z.1 ∂P₁.prod P₂) +
        ∫ z, MeasureTheory.llr P₂ Q₂ z.2 ∂P₁.prod P₂ := by
          rw [integral_add (h₁int.comp_fst P₂) (h₂int.comp_snd P₁)]
    _ = (∫ x, MeasureTheory.llr P₁ Q₁ x ∂(Measure.map Prod.fst (P₁.prod P₂))) +
        ∫ y, MeasureTheory.llr P₂ Q₂ y ∂(Measure.map Prod.snd (P₁.prod P₂)) := by
          rw [← integral_map measurable_fst.aemeasurable
                (MeasureTheory.stronglyMeasurable_llr P₁ Q₁).aestronglyMeasurable,
              ← integral_map measurable_snd.aemeasurable
                (MeasureTheory.stronglyMeasurable_llr P₂ Q₂).aestronglyMeasurable]
    _ = (∫ x, MeasureTheory.llr P₁ Q₁ x ∂P₁) +
        ∫ y, MeasureTheory.llr P₂ Q₂ y ∂P₂ := by
          simp [measurePreserving_fst, measurePreserving_snd]

end StatisticalRL.PrelimKL
