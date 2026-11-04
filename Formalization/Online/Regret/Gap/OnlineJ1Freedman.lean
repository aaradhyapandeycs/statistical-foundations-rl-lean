import Formalization.Online.Regret.Gap.OnlineJ1ActualVarianceSum

/-! Actual-law variance and gap proof component: OnlineJ1Freedman.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1FreeState : MeasurableSpace State := ⊤
noncomputable local instance j1FreeSample (H K : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤
theorem onlineJ1Freedman_fixed_time
    (H K j : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (L c₁ c₂ δ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hJ : 0 < j) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    1 - δ ≤ μ.real {sample |
      |incrementSum (onlineJ1PaddedY H K hH E fallback L c₁ c₂) (K * H) sample| ≤
        Real.sqrt (8 * max
          (predictableSecondMomentSum μ ℱ
            (onlineJ1PaddedY H K hH E fallback L c₁ c₂) (K * H) sample)
          (((K : ℝ) * (H : ℝ)^3) / (2 : ℝ)^j) * Real.log (2 * j / δ)) +
        (4 / 3) * (H : ℝ) * Real.log (2 * j / δ)} := by
  classical
  dsimp
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineJ1PaddedY H K hH E fallback L c₁ c₂
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hX : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n) := by
    intro n
    exact (onlineJ1PaddedY_measurable_next H K hH E fallback L c₁ c₂ n).stronglyMeasurable
  have hb : ∀ n, ∀ᵐ sample ∂μ, |X n sample| ≤ (H : ℝ) := by
    intro n
    exact Filter.Eventually.of_forall
      (fun sample => onlineJ1PaddedY_abs_le H K hH E fallback L c₁ c₂ n sample)
  have hc : ∀ n, μ[X n | ℱ n] =ᵐ[μ] fun _ => 0 := by
    intro n
    exact onlineJ1PaddedY_condExp_zero H K hH E ρ fallback L c₁ c₂ n
  have hcap := onlineJ1PredictableSecondMomentSum_le_KH3
    H K hH E ρ fallback L c₁ c₂
  exact StatisticalRL.freedman_source_bound μ ℱ X ((H : ℝ))
    ((K : ℝ) * (H : ℝ)^3) (by positivity) (by positivity)
    hX hb hc (K * H) j hJ hcap δ hδ hδ1

end StatisticalRL.OnlineRL
