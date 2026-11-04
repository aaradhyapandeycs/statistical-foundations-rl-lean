import Formalization.Online.Regret.T4.OnlineT4SuffixTelescope

/-! Same-experiment suffix proof component: OnlineT4SuffixCentering.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance suffixCenterStateMeasurable : MeasurableSpace State := ⊤

theorem onlineT4SuffixEpisodeIncrement_measurable_end
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (j : ℕ) (k : Fin K) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner ((k.val + 1) * H)]
      (onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k) := by
  unfold onlineT4SuffixEpisodeIncrement
  apply Finset.measurable_fun_sum
  intro h hh
  have hindex : k.val * H + h.val + 1 ≤ (k.val + 1) * H := by
    rw [Nat.succ_mul]
    omega
  exact (onlineT4ActualStep_measurable_next H K hH E fallback planner k h).mono
    (onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner hindex) le_rfl

theorem onlineT4SuffixEpisodeIncrement_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : ℕ) (k : Fin K) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k |
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
        MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := le_top
    have hc := onlineT4ActualStep_condExp_zero H K hH E ρ fallback planner k h
    have ht := MeasureTheory.condExp_condExp_of_le
      (μ := μ) (f := onlineT4ActualStep H K hH E fallback planner k h) hm hle
    have hz : μ[μ[onlineT4ActualStep H K hH E fallback planner k h | F n] |
        F (k.val * H)] =ᵐ[μ] 0 := by
      simpa only [MeasureTheory.condExp_zero] using
        (MeasureTheory.condExp_congr_ae (m := F (k.val * H)) hc)
    exact ht.symm.trans hz
  let S := Finset.univ.filter (fun h : Fin H => j ≤ h.val)
  have hf : onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k =
      ∑ h ∈ S, onlineT4ActualStep H K hH E fallback planner k h := by
    funext sample
    simp only [onlineT4SuffixEpisodeIncrement, S, Finset.sum_apply]
  have hs := MeasureTheory.condExp_finset_sum (μ := μ) (s := S)
    (f := fun h : Fin H => onlineT4ActualStep H K hH E fallback planner k h)
    (fun h hh => Integrable.of_finite) (F (k.val * H))
  have hall : ∀ᵐ sample ∂μ, ∀ h : Fin H,
      (μ[onlineT4ActualStep H K hH E fallback planner k h | F (k.val * H)]) sample = 0 :=
    ae_all_iff.mpr hcenter
  change μ[onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k |
    F (k.val * H)] =ᵐ[μ] 0
  rw [hf]
  filter_upwards [hs, hall] with sample hsum hzero
  simpa only [Finset.sum_apply, hzero, Finset.sum_const_zero] using hsum

end StatisticalRL.OnlineRL
