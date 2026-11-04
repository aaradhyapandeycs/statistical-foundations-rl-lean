import Formalization.Online.Regret.T8.OnlineT8VarianceSum

/-! Actual-law variance and gap proof component: OnlineT8Freedman.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8FreeState : MeasurableSpace State := ⊤
noncomputable local instance t8FreeSample (H K : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤
theorem onlineT8Freedman_fixed_time
    (H K j : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ δ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hJ : 0 < j) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    1 - δ ≤ μ.real {sample |
      |incrementSum (onlineT8PaddedY H K hH E fallback planner L c₁ c₂) (K * H) sample| ≤
        Real.sqrt (8 * max
          (predictableSecondMomentSum μ ℱ
            (onlineT8PaddedY H K hH E fallback planner L c₁ c₂) (K * H) sample)
          (((K : ℝ) * (H : ℝ)^5) / (2 : ℝ)^j) * Real.log (2 * j / δ)) +
        (4 / 3) * (H : ℝ)^2 * Real.log (2 * j / δ)} := by
  classical
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineT8PaddedY H K hH E fallback planner L c₁ c₂
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n) := by
    intro n
    exact (onlineT8PaddedY_measurable_next H K hH E fallback planner L c₁ c₂ n).stronglyMeasurable
  have hb : ∀ n, ∀ᵐ sample ∂μ, |X n sample| ≤ (H : ℝ)^2 := by
    intro n
    exact Filter.Eventually.of_forall
      (fun sample => onlineT8PaddedY_abs_le H K hH E fallback planner
        L c₁ c₂ hL hc₁ hc₂ n sample)
  have hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ => 0 := by
    intro n
    exact onlineT8PaddedY_condExp_zero H K hH E ρ fallback planner L c₁ c₂ n
  have hcap := onlineT8PredictableSecondMomentSum_le_KH5
    H K hH E ρ fallback planner L c₁ c₂ hL hc₁ hc₂
  exact StatisticalRL.freedman_source_bound μ ℱ X ((H : ℝ)^2)
    ((K : ℝ) * (H : ℝ)^5) (by positivity) (by positivity)
    hX hb hc (K * H) j hJ hcap δ hδ hδ1

end StatisticalRL.OnlineRL
