import Formalization.Online.LowerBound.GaussianBanditMinimax
import Formalization.Online.Bandit.UCBRegret

/-!
# Minimax optimality of UCB up to logarithmic factors (Remark 5.12, restricted)

Combines the Gaussian-bandit lower bound `minimax_lower_bound` with Theorem 5.1
(`Bandit.ucb_regret_bounds`, deterministic tie rules): `8√(ATL) = 128√L · (1/16)√(AT)`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace StatisticalRL.GaussianBanditLB

open StatisticalRL.Bandit

theorem ucb_minimax_optimal (A T : ℕ) (δ : ℝ) (tie : ℕ → Finset (Fin A) → Fin A)
    (htie : ∀ t s, s.Nonempty → tie t s ∈ s) (hA : 2 ≤ A) (hAT : A ≤ T) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    let L := Real.log ((T : ℝ) ^ 2 / δ)
    ∃ μ : Fin A → Fin A → ℝ, (∀ i a, μ i a ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A),
        (∀ t, Measurable (Function.uncurry (arm t))) →
        ∃ i : Fin A,
          Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => regret arm (μ i) T ω.1 ω.2)
            (ν.prod (gaussianNoiseTable T A)) ∧
          (1 / 16 : ℝ) * Real.sqrt ((A : ℝ) * T) ≤
            ∫ ω, regret arm (μ i) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A)) ∧
          ∀ r : Fin A → ℝ, (∀ a, r a ∈ Set.Icc (0 : ℝ) 1) →
            Integrable (fun z : Fin T → Fin A → ℝ =>
                (T : ℝ) * (⨆ a, r a) - ∑ t, r (ucbAction tie L r z t))
              (gaussianNoiseTable T A) ∧
            ∫ z, ((T : ℝ) * (⨆ a, r a) - ∑ t, r (ucbAction tie L r z t))
                ∂gaussianNoiseTable T A ≤
              128 * Real.sqrt L *
                ∫ ω, regret arm (μ i) T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A)) := by
  intro L
  obtain ⟨μ, hμ, h⟩ := minimax_lower_bound A T hA hAT
  refine ⟨μ, hμ, fun Seed _ ν _ arm harm => ?_⟩
  obtain ⟨i, hint, hlb⟩ := h Seed ν arm harm
  refine ⟨i, hint, hlb, fun r hr => ?_⟩
  obtain ⟨hI, hU, -⟩ := ucb_regret_bounds A T r δ tie htie hA hAT hr hδ0 hδ1
  refine ⟨hI, hU.trans ?_⟩
  have hT : (2 : ℝ) ≤ T := by exact_mod_cast (show 2 ≤ T by omega)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hAT0 : (0 : ℝ) ≤ (A : ℝ) * T := by positivity
  rw [Real.sqrt_mul hAT0 L]
  calc 8 * (Real.sqrt ((A : ℝ) * T) * Real.sqrt L)
      = 128 * Real.sqrt L * ((1 / 16 : ℝ) * Real.sqrt ((A : ℝ) * T)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlb (by positivity)

end StatisticalRL.GaussianBanditLB
