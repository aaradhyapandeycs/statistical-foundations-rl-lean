import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Formalization.PrelimKL.KLBinaryProductLLRAdd
import Formalization.PrelimKL.KLBinaryProductFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.PrelimKL

/-- Finite KL of a binary product forces finite KL of its first marginal. -/
theorem binary_product_finite_klDiv_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (hprod : InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) ≠ ∞) :
    InformationTheory.klDiv P₁ Q₁ ≠ ∞ := by
  have hprodAC : P₁.prod P₂ ≪ Q₁.prod Q₂ :=
    (InformationTheory.klDiv_ne_top_iff.mp hprod).1
  have hprodInt : Integrable (MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂))
      (P₁.prod P₂) := (InformationTheory.klDiv_ne_top_iff.mp hprod).2
  have hP1Q1 : P₁ ≪ Q₁ := by
    have hmap : Measure.map Prod.fst (P₁.prod P₂) ≪
        Measure.map Prod.fst (Q₁.prod Q₂) := hprodAC.map measurable_fst
    simpa only [measurePreserving_fst.map_eq] using hmap
  have hsumInt : Integrable
      (fun z : α × β ↦ MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2)
      (P₁.prod P₂) :=
    (integrable_congr (llr_prod_eq_add_ae P₁ Q₁ P₂ Q₂ hP1Q1
      ((by
        have hmap : Measure.map Prod.snd (P₁.prod P₂) ≪
            Measure.map Prod.snd (Q₁.prod Q₂) := hprodAC.map measurable_snd
        simpa only [measurePreserving_snd.map_eq] using hmap)))
      ).mp hprodInt
  have hsections : ∀ᵐ y ∂P₂,
      Integrable (fun x : α ↦ MeasureTheory.llr P₁ Q₁ x +
        MeasureTheory.llr P₂ Q₂ y) P₁ := hsumInt.prod_left_ae
  obtain ⟨y, hy⟩ := hsections.exists
  have hleftInt : Integrable (MeasureTheory.llr P₁ Q₁) P₁ := by
    exact (integrable_add_const_iff
      (f := MeasureTheory.llr P₁ Q₁) (c := MeasureTheory.llr P₂ Q₂ y)).mp hy
  exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hP1Q1, hleftInt⟩

/-- Finite coordinate KL divergences imply finite binary product KL. -/
theorem binary_product_finite_klDiv_of_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (h₁ : InformationTheory.klDiv P₁ Q₁ ≠ ∞)
    (h₂ : InformationTheory.klDiv P₂ Q₂ ≠ ∞) :
    InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) ≠ ∞ := by
  have h₁ac : P₁ ≪ Q₁ := (InformationTheory.klDiv_ne_top_iff.mp h₁).1
  have h₂ac : P₂ ≪ Q₂ := (InformationTheory.klDiv_ne_top_iff.mp h₂).1
  have h₁int : Integrable (MeasureTheory.llr P₁ Q₁) P₁ :=
    (InformationTheory.klDiv_ne_top_iff.mp h₁).2
  have h₂int : Integrable (MeasureTheory.llr P₂ Q₂) P₂ :=
    (InformationTheory.klDiv_ne_top_iff.mp h₂).2
  have hprodac : P₁.prod P₂ ≪ Q₁.prod Q₂ := h₁ac.prod h₂ac
  have hllr := llr_prod_eq_add_ae P₁ Q₁ P₂ Q₂ h₁ac h₂ac
  have hsumInt : Integrable
      (fun z : α × β ↦ MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2)
      (P₁.prod P₂) := (h₁int.comp_fst P₂).add (h₂int.comp_snd P₁)
  have hprodInt : Integrable (MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂))
      (P₁.prod P₂) := (integrable_congr hllr).2 hsumInt
  exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hprodac, hprodInt⟩

/-- Finite KL of a binary product forces finite KL of its second marginal. -/
theorem binary_product_finite_klDiv_right
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (hprod : InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) ≠ ∞) :
    InformationTheory.klDiv P₂ Q₂ ≠ ∞ := by
  have hprodAC : P₁.prod P₂ ≪ Q₁.prod Q₂ :=
    (InformationTheory.klDiv_ne_top_iff.mp hprod).1
  have hprodInt : Integrable (MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂))
      (P₁.prod P₂) := (InformationTheory.klDiv_ne_top_iff.mp hprod).2
  have hP₂Q₂ : P₂ ≪ Q₂ := by
    have hmap : Measure.map Prod.snd (P₁.prod P₂) ≪
        Measure.map Prod.snd (Q₁.prod Q₂) := hprodAC.map measurable_snd
    simpa only [measurePreserving_snd.map_eq] using hmap
  have hsumInt : Integrable
      (fun z : α × β ↦ MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2)
      (P₁.prod P₂) :=
    (integrable_congr (llr_prod_eq_add_ae P₁ Q₁ P₂ Q₂
      ((by
        have hmap : Measure.map Prod.fst (P₁.prod P₂) ≪
            Measure.map Prod.fst (Q₁.prod Q₂) := hprodAC.map measurable_fst
        simpa only [measurePreserving_fst.map_eq] using hmap)) hP₂Q₂)).mp hprodInt
  have hsections : ∀ᵐ x ∂P₁,
      Integrable (fun y : β ↦ MeasureTheory.llr P₁ Q₁ x +
        MeasureTheory.llr P₂ Q₂ y) P₂ := hsumInt.prod_right_ae
  obtain ⟨x, hx⟩ := hsections.exists
  have hrightInt : Integrable (MeasureTheory.llr P₂ Q₂) P₂ := by
    exact (integrable_const_add_iff
      (f := MeasureTheory.llr P₂ Q₂) (c := MeasureTheory.llr P₁ Q₁ x)).mp hx
  exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hP₂Q₂, hrightInt⟩

/-- Extended-valued binary product KL tensorization, including infinite coordinate values. -/
theorem binary_product_klDiv_add
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) =
      InformationTheory.klDiv P₁ Q₁ + InformationTheory.klDiv P₂ Q₂ := by
  by_cases h₁top : InformationTheory.klDiv P₁ Q₁ = ∞
  · have hprod : InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) = ∞ := by
      by_contra hne
      exact (binary_product_finite_klDiv_left P₁ Q₁ P₂ Q₂ hne) h₁top
    simp [h₁top, hprod]
  · by_cases h₂top : InformationTheory.klDiv P₂ Q₂ = ∞
    · have hprod : InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) = ∞ := by
        by_contra hne
        exact (binary_product_finite_klDiv_right P₁ Q₁ P₂ Q₂ hne) h₂top
      simp [h₂top, hprod]
    · have hprod : InformationTheory.klDiv (P₁.prod P₂) (Q₁.prod Q₂) ≠ ∞ :=
        binary_product_finite_klDiv_of_finite P₁ Q₁ P₂ Q₂ h₁top h₂top
      have hsum : InformationTheory.klDiv P₁ Q₁ + InformationTheory.klDiv P₂ Q₂ ≠ ∞ :=
        ENNReal.add_ne_top.mpr ⟨h₁top, h₂top⟩
      exact (ENNReal.toReal_eq_toReal_iff' hprod hsum).mp (by
        rw [ENNReal.toReal_add h₁top h₂top]
        exact binary_product_toReal_klDiv_of_finite P₁ Q₁ P₂ Q₂ h₁top h₂top)

end StatisticalRL.PrelimKL
