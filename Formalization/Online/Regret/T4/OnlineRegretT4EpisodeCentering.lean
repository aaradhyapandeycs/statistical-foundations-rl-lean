import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeSum

/-! actual episode-boundary centering and measurability.
The concentration conclusion is a separate application. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t4EpisodeCenterStateMeasurable : MeasurableSpace State := ⊤

theorem onlineT4ActualStep_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner
      (k.val * H + h.val + 1)]
      (onlineT4ActualStep H K hH E fallback planner k h) := by
  let θ := fun (_initial : Fin K → State) history =>
    onlineT4PolicyTailAtPrefix H hH E planner k.val h history
  have hf : onlineT4ActualStep H K hH E fallback planner k h =
      -onlinePredictableObservedY H K (K * H) hH E fallback planner
        (k.val * H + h.val) θ := by
    funext sample
    rfl
  rw [hf]
  exact (onlinePredictableObservedY_measurable_next H K (K * H) hH E fallback
    planner (k.val * H + h.val) θ).neg

/-- The episode increment is observable at the end of that actual episode. -/
theorem onlineT4EpisodeIncrement_measurable_end
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (k : Fin K) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner ((k.val + 1) * H)]
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k) := by
  have hf : (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
      onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k) =
        fun sample => ∑ h : Fin H, onlineT4ActualStep H K hH E fallback planner k h sample := by
    funext sample
    exact onlineT4EpisodeIncrement_eq_sumActualStep H K hH E fallback planner k sample
  rw [hf]
  apply Finset.measurable_fun_sum
  intro h hh
  have hindex : k.val * H + h.val + 1 ≤ (k.val + 1) * H := by
    rw [Nat.succ_mul]
    omega
  exact (onlineT4ActualStep_measurable_next H K hH E fallback planner k h).mono
    (onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner hindex) le_rfl

/-- Conditional mean of the actual whole-episode increment is zero given its
completed history and the source reset vector. The claim is derived from the
actual centered transition residuals and the prefix-field tower property. -/
theorem onlineT4EpisodeIncrement_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (k : Fin K) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)] =ᵐ[μ] 0 := by
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner
  have hcenter (h : Fin H) :
      μ[onlineT4ActualStep H K hH E fallback planner k h | F (k.val * H)] =ᵐ[μ] 0 := by
    let n := k.val * H + h.val
    have hm : F (k.val * H) ≤ F n :=
      onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner (Nat.le_add_right _ _)
    have hle : F n ≤ (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable :
        MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := by
      exact le_top
    have hc := onlineT4ActualStep_condExp_zero H K hH E ρ fallback planner k h
    have ht := MeasureTheory.condExp_condExp_of_le
      (μ := μ) (f := onlineT4ActualStep H K hH E fallback planner k h) hm hle
    have hz : μ[μ[onlineT4ActualStep H K hH E fallback planner k h | F n] |
        F (k.val * H)] =ᵐ[μ] 0 := by
      simpa only [MeasureTheory.condExp_zero] using
        (MeasureTheory.condExp_congr_ae (m := F (k.val * H)) hc)
    exact ht.symm.trans hz
  have hf : (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
      onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k) =
        ∑ h : Fin H, onlineT4ActualStep H K hH E fallback planner k h := by
    funext sample
    simpa only [Finset.sum_apply] using
      onlineT4EpisodeIncrement_eq_sumActualStep H K hH E fallback planner k sample
  have hs := MeasureTheory.condExp_finset_sum (μ := μ) (s := Finset.univ)
    (f := fun h : Fin H => onlineT4ActualStep H K hH E fallback planner k h)
    (fun h hh => Integrable.of_finite) (F (k.val * H))
  have hall : ∀ᵐ sample ∂μ, ∀ h : Fin H,
      (μ[onlineT4ActualStep H K hH E fallback planner k h | F (k.val * H)]) sample = 0 := by
    exact ae_all_iff.mpr hcenter
  change μ[(fun sample => onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k) |
    F (k.val * H)] =ᵐ[μ] 0
  rw [hf]
  filter_upwards [hs, hall] with sample hsum hzero
  simpa only [Finset.sum_apply, hzero, Finset.sum_const_zero] using hsum

end StatisticalRL.OnlineRL
