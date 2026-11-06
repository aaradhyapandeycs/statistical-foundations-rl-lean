import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Formalization.PrelimKL.KLBinaryProductRNDerivative

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.PrelimKL

/-- Under coordinate absolute continuity, the product log-likelihood ratio is the sum of
coordinate log-likelihood ratios almost everywhere under the product numerator measure. -/
theorem llr_prod_eq_add_ae
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P₁ Q₁ : Measure α) (P₂ Q₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (h₁ac : P₁ ≪ Q₁) (h₂ac : P₂ ≪ Q₂) :
    MeasureTheory.llr (P₁.prod P₂) (Q₁.prod Q₂) =ᵐ[P₁.prod P₂]
      fun z : α × β ↦ MeasureTheory.llr P₁ Q₁ z.1 + MeasureTheory.llr P₂ Q₂ z.2 := by
  let f := P₁.rnDeriv Q₁
  let g := P₂.rnDeriv Q₂
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
  filter_upwards [hRNprod, h₁posProd, h₂posProd, h₁finiteProd, h₂finiteProd]
    with z hderiv h₁p h₂p h₁lt h₂lt
  simp only [MeasureTheory.llr] at hderiv ⊢
  rw [hderiv, ENNReal.toReal_mul,
    Real.log_mul (ENNReal.toReal_pos h₁p.ne' h₁lt.ne).ne'
      (ENNReal.toReal_pos h₂p.ne' h₂lt.ne).ne']

end StatisticalRL.PrelimKL
