import Formalization.Online.Predictable.OnlinePredictableObservedProcess
import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVariancePotential
import Formalization.Online.Regret.Definitions

/-! Actual-law variance and gap proof component: OnlineVariancePotentialCentering.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceCenterStateMeasurable : MeasurableSpace State := ⊤

/-- The predictable value of the remaining fixed-policy variance potential,
chosen from completed data before the current successor is observed. -/
noncomputable def onlineVariancePotentialTest
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ)
    (_initial : Fin K → State) (history : List (OnlineMDPRow State Action H × State)) : State → ℝ :=
  let π := onlineCappedEpisodePolicy H hH E history k.val L c₁ c₂
  let stages := EnvironmentStage.controlled (List.ofFn E) π
  finiteTrajectoryVariancePotential (stages.drop (h.val + 1))

noncomputable def onlineVariancePotentialResidual
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  onlinePredictableObservedY H K (K * H) hH E fallback planner
    (k.val * H + h.val) (onlineVariancePotentialTest H K hH E k h L c₁ c₂) sample

/-- The sum of actual one-step potential residuals has conditional mean zero
at the episode boundary, by the proved one-step predictable-test theorem and
prefix-field tower. -/
theorem onlineVariancePotentialResidual_sum_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (k : Fin K) (L c₁ c₂ : ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => ∑ h : Fin H, onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ sample) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)] =ᵐ[μ] 0 := by
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner
  have hcenter (h : Fin H) :
      μ[onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ | F (k.val * H)] =ᵐ[μ] 0 := by
    let n := k.val * H + h.val
    let m := K * H - (n + 1)
    have hn : n + 1 ≤ K * H := by
      dsimp [n]
      calc
        k.val * H + h.val + 1 ≤ (k.val + 1) * H := by rw [Nat.succ_mul]; omega
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
    have hT : K * H = (m + 1) + n := by dsimp [m]; omega
    have hm : F (k.val * H) ≤ F n :=
      onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner (Nat.le_add_right _ _)
    have hle : F n ≤ (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := by
      intro s hs
      change @MeasurableSet _ ⊤ s
      trivial
    have hc := onlinePredictableObservedY_condExp_zero H K (K * H) hH E ρ fallback planner n m hT
      (onlineVariancePotentialTest H K hH E k h L c₁ c₂)
    have ht := MeasureTheory.condExp_condExp_of_le
      (μ := μ) (f := onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂) hm hle
    have hz : μ[μ[onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ | F n] |
        F (k.val * H)] =ᵐ[μ] 0 := by
      simpa only [MeasureTheory.condExp_zero] using
        (MeasureTheory.condExp_congr_ae (m := F (k.val * H)) hc)
    exact ht.symm.trans hz
  have hs := MeasureTheory.condExp_finset_sum (μ := μ) (s := Finset.univ)
    (f := fun h : Fin H => onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂)
    (fun h hh => Integrable.of_finite) (F (k.val * H))
  have hall : ∀ᵐ sample ∂μ, ∀ h : Fin H,
      (μ[onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ | F (k.val * H)]) sample = 0 := by
    exact ae_all_iff.mpr hcenter
  change μ[(fun sample => ∑ h : Fin H, onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ sample) |
    F (k.val * H)] =ᵐ[μ] 0
  have heq : (fun sample => ∑ h : Fin H, onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ sample) =
      ∑ h : Fin H, onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ := by
    funext sample
    simp only [Finset.sum_apply]
  rw [heq]
  filter_upwards [hs, hall] with sample hsum hzero
  simpa only [Finset.sum_apply, hzero, Finset.sum_const_zero] using hsum
end StatisticalRL.OnlineRL
