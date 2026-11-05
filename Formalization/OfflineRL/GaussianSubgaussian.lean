import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.HasLaw

/-! Gaussian noise is 1-sub-Gaussian.

For the standard Gaussian reward noise in `chapters/offlineRL.tex:243–260`, this
module proves the one-variable law-to-sub-Gaussian bridge. It makes no claim about
independence, conditional laws, count concentration, or the offline regret result.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StatisticalRL.OfflineRL

/-- The standard Gaussian law satisfies the sub-Gaussian MGF bound with proxy `1`. -/
theorem hasSubgaussianMGF_id_gaussianReal_zero_one :
    HasSubgaussianMGF id (1 : ℝ≥0) (gaussianReal 0 1) where
  integrable_exp_mul t := by
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t)
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- Proposed contract (`offline-gaussian-api-contract-v1/CONTRACT.md`): if `X` has
law `𝒩(m, 1)` under `μ`, then `X - m` is `1`-sub-Gaussian under `μ`. No
measurability, integrability, probability-instance or independence premise
beyond `HasLaw`. -/
theorem hasSubgaussianMGF_sub_of_hasLaw_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (m : ℝ)
    (hX : HasLaw X (gaussianReal m 1) μ) :
    HasSubgaussianMGF (fun ω => X ω - m) 1 μ := by
  have hsub : HasLaw (fun x : ℝ => x - m) (gaussianReal 0 1) (gaussianReal m 1) :=
    { aemeasurable := (measurable_id.sub_const m).aemeasurable
      map_eq := by rw [gaussianReal_map_sub_const, sub_self] }
  have hc : HasLaw (fun ω => X ω - m) (gaussianReal 0 1) μ := hsub.comp hX
  rw [← HasSubgaussianMGF.id_map_iff hc.aemeasurable, hc.map_eq]
  exact hasSubgaussianMGF_id_gaussianReal_zero_one

end StatisticalRL.OfflineRL
