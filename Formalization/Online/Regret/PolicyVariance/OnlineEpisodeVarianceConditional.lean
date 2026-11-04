import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceIdentity

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceConditional.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceConditionalStateMeasurable : MeasurableSpace State := ⊤

/-- Initial frozen variance potential is computed solely from the full reset
vector and the pre-episode transcript. -/
noncomputable def onlineEpisodeInitialVariancePotentialFromPrefix
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (k : Fin K) (L c₁ c₂ : ℝ)
    (observed : (Fin K → State) × List (OnlineMDPRow State Action H × State)) : ℝ :=
  let π := onlineCappedEpisodePolicy H hH E observed.2 k.val L c₁ c₂
  let stages := EnvironmentStage.controlled (List.ofFn E) π
  finiteTrajectoryVariancePotential stages (observed.1 k)

noncomputable def onlineEpisodeInitialVariancePotential
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  onlineEpisodeInitialVariancePotentialFromPrefix H K hH E k (Real.log (1 / δ)) c₁ c₂
    (onlineT3CommonPrefixObservation H K (K * H) hH fallback
      (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (k.val * H) sample)

theorem onlineEpisodeInitialVariancePotential_measurable
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback
      (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (k.val * H)]
      (onlineEpisodeInitialVariancePotential H K hH E fallback δ c₁ c₂ k) := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  have hobs : @Measurable ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))
      ((Fin K → State) × List (OnlineMDPRow State Action H × State))
      (onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)) ⊤
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (k.val * H)) := by
    intro s hs
    exact (MeasurableSpace.measurableSet_comap).2 ⟨s, hs, rfl⟩
  have hf : @Measurable ((Fin K → State) × List (OnlineMDPRow State Action H × State))
      ℝ ⊤ (inferInstance : MeasurableSpace ℝ)
      (onlineEpisodeInitialVariancePotentialFromPrefix H K hH E k (Real.log (1 / δ)) c₁ c₂) := by
    intro s hs
    exact MeasurableSpace.measurableSet_top
  exact hf.comp hobs

/-- The actual episode's sum of true policy transition variances has
conditional expectation at most H² given its full reset vector and completed
history. The static policy is frozen before every within-episode successor. -/
theorem onlineActualEpisodePolicyVariance_condExp_le_horizon_sq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)] ≤ᵐ[μ] fun _ => (H : ℝ)^2 := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)
  let initialPot := onlineEpisodeInitialVariancePotential H K hH E fallback δ c₁ c₂ k
  let residual := fun sample => ∑ h : Fin H,
    onlineVariancePotentialResidual H K hH E fallback planner k h (Real.log (1 / δ)) c₁ c₂ sample
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hF : F ≤ (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable : MeasurableSpace
      ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := by
    intro s hs
    change @MeasurableSet _ ⊤ s
    trivial
  have hmeas := onlineEpisodeInitialVariancePotential_measurable H K hH E fallback δ c₁ c₂ k
  have hself := MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) hF hmeas.stronglyMeasurable Integrable.of_finite
  have hzero := onlineVariancePotentialResidual_sum_condExp_zero H K hH E ρ fallback planner k (Real.log (1 / δ)) c₁ c₂
  have hsub := MeasureTheory.condExp_sub (μ := μ) (f := initialPot) (g := residual)
    Integrable.of_finite Integrable.of_finite F
  have hid : (fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) =
      initialPot - residual := by
    funext sample
    have hh := onlineActualEpisodePolicyVariance_eq_potential_sub_residuals H K hH E fallback δ c₁ c₂ k sample
    have hpolicy (history : List (OnlineMDPRow State Action H × State)) :
        onlineCappedEpisodePolicy H hH E (history.take (k.val * H)) k.val (Real.log (1 / δ)) c₁ c₂ =
          onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂ := by
      funext t s
      simp only [onlineCappedEpisodePolicy, List.take_take, Nat.min_self]
    simpa only [Pi.sub_apply, initialPot, residual, onlineEpisodeInitialVariancePotential,
      onlineEpisodeInitialVariancePotentialFromPrefix, onlineT3CommonPrefixObservation,
      onlineT3CommonFullHistory, hpolicy] using hh
  rw [hid]
  filter_upwards [hsub, hzero] with sample hs hz
  have hbounded : initialPot sample ≤ (H : ℝ)^2 := by
    unfold initialPot onlineEpisodeInitialVariancePotential onlineEpisodeInitialVariancePotentialFromPrefix
    have hh := finiteTrajectoryVariancePotential_range
      (EnvironmentStage.controlled (List.ofFn E)
        (onlineCappedEpisodePolicy H hH E
          (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (k.val * H) sample).2
          k.val (Real.log (1 / δ)) c₁ c₂)) (sample.1 k)
    have hlen : (EnvironmentStage.controlled (List.ofFn E)
        (onlineCappedEpisodePolicy H hH E
          (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (k.val * H) sample).2
          k.val (Real.log (1 / δ)) c₁ c₂)).length = H := by
      rw [onlineControlledStages_length]
      simp
    rw [hlen] at hh
    simpa only [onlineT3CommonPrefixObservation] using hh.2
  change μ[residual | F] sample = 0 at hz
  rw [hs, hself]
  simpa only [Pi.sub_apply, hz, sub_zero] using hbounded
end StatisticalRL.OnlineRL
