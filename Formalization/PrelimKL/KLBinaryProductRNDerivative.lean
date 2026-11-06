import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Radon–Nikodym derivative of a product measure under product probabilities, used for
`lem:KL-tensorize` (`chapters/prelim.tex:1313–1319`). -/

open MeasureTheory
open scoped ENNReal

namespace StatisticalRL.PrelimKL

/-- The product likelihood density is the product of the coordinate densities, almost everywhere
under the reference product measure. The proof constructs this density through the actual
`Measure.prod` and `withDensity` operations. -/
theorem rnDeriv_prod_eq_mul_ae
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (κ rho : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] [IsProbabilityMeasure rho]
    (hμν : μ ≪ ν) (hκrho : κ ≪ rho) :
    (μ.prod κ).rnDeriv (ν.prod rho) =ᵐ[ν.prod rho]
      fun z : α × β ↦ μ.rnDeriv ν z.1 * κ.rnDeriv rho z.2 := by
  have hμdens : ν.withDensity (μ.rnDeriv ν) = μ := by
    calc
      ν.withDensity (μ.rnDeriv ν) =
          μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) := by
            simp [Measure.singularPart_eq_zero_of_ac hμν]
      _ = μ := Measure.singularPart_add_rnDeriv μ ν
  have hκdens : rho.withDensity (κ.rnDeriv rho) = κ := by
    calc
      rho.withDensity (κ.rnDeriv rho) =
          κ.singularPart rho + rho.withDensity (κ.rnDeriv rho) := by
            simp [Measure.singularPart_eq_zero_of_ac hκrho]
      _ = κ := Measure.singularPart_add_rnDeriv κ rho
  have hprodDensity : μ.prod κ =
      (ν.prod rho).withDensity (fun z : α × β ↦
        μ.rnDeriv ν z.1 * κ.rnDeriv rho z.2) := by
    calc
      μ.prod κ =
          (ν.withDensity (μ.rnDeriv ν)).prod (rho.withDensity (κ.rnDeriv rho)) := by
            rw [hμdens, hκdens]
      _ = (ν.prod rho).withDensity (fun z : α × β ↦
          μ.rnDeriv ν z.1 * κ.rnDeriv rho z.2) :=
        MeasureTheory.prod_withDensity
          (μ := ν) (ν := rho) (f := μ.rnDeriv ν) (g := κ.rnDeriv rho)
          (Measure.measurable_rnDeriv μ ν) (Measure.measurable_rnDeriv κ rho)
  symm
  apply Measure.eq_rnDeriv₀
  · exact (((Measure.measurable_rnDeriv μ ν).comp measurable_fst).mul
      ((Measure.measurable_rnDeriv κ rho).comp measurable_snd)).aemeasurable
  · exact Measure.MutuallySingular.zero_left
  · simpa only [zero_add] using hprodDensity

end StatisticalRL.PrelimKL
