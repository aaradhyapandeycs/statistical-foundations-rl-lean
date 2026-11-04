import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceMGF

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceSumBridge.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceBridgeState : MeasurableSpace State := ⊤
noncomputable local instance varianceBridgeSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineActualT6Policy_le_centered_sum_ae
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    ∀ᵐ sample ∂μ,
      onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
        (K : ℝ) * (H : ℝ)^2 +
          ∑ n ∈ Finset.range K, onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n sample := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  have hclip (k : Fin K) : ∀ᵐ sample ∂μ,
      onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k sample ≤ (H : ℝ)^2 := by
    filter_upwards [onlineEpisodeVarianceClippedMean_ae_eq H K hH E ρ fallback δ c₁ c₂ k,
      onlineActualEpisodePolicyVariance_condExp_le_horizon_sq H K hH E ρ fallback δ c₁ c₂ k] with sample he hb
    exact he.le.trans hb
  have hall : ∀ᵐ sample ∂μ, ∀ k : Fin K,
      onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k sample ≤ (H : ℝ)^2 :=
    ae_all_iff.mpr hclip
  filter_upwards [hall] with sample hs
  rw [← onlineActualEpisodePolicyVariance_sum_eq_T6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂]
  rw [Finset.sum_range]
  have hsum : (∑ k : Fin K, onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k sample) ≤
      (K : ℝ) * (H : ℝ)^2 := by
    calc
      _ ≤ ∑ _k : Fin K, (H : ℝ)^2 := Finset.sum_le_sum (fun k _ => hs k)
      _ = (K : ℝ) * (H : ℝ)^2 := by simp
  have heq : (∑ k : Fin K, onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ k.val sample) =
      (∑ k : Fin K, onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) -
        ∑ k : Fin K, onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k sample := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [onlineVariancePaddedY, dif_pos k.isLt]
  rw [heq]
  linarith
end StatisticalRL.OnlineRL
