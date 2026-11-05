import Formalization.Online.Regret.MVP.T34.MVPActualT3Freedman
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT3PeelState : MeasurableSpace State := ⊤
noncomputable local instance mvpT3PeelSample (H K : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤
theorem mvpT3Freedman_peeled_integer
    (H K j : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ δ' : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hj : 0 < j) (hδ' : 0 < δ') (hbranch : 2 * j * δ' < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    1 - 2 * j * δ' ≤ μ.real {sample |
      |incrementSum (mvpT3PaddedY H K hH E fallback planner L c₁ c₂)
          (K * H) sample| ≤
        Real.sqrt (8 * max
          (predictableSecondMomentSum μ ℱ
            (mvpT3PaddedY H K hH E fallback planner L c₁ c₂) (K * H) sample)
          (((K : ℝ) * (H : ℝ)^3) / (2 : ℝ)^j) * Real.log (1 / δ')) +
        (4 / 3) * (H : ℝ) * Real.log (1 / δ')} := by
  classical
  dsimp
  let δF : ℝ := 2 * j * δ'
  have hδF : 0 < δF := by dsimp [δF]; positivity
  have hδF1 : δF < 1 := by simpa [δF] using hbranch
  have hfixed := mvpT3Freedman_fixed_time H K j hH E ρ fallback planner
    L c₁ c₂ δF hL hc₁ hc₂ hj hδF hδF1
  have hlog : Real.log (2 * (j : ℝ) / δF) = Real.log (1 / δ') := by
    congr 1
    dsimp [δF]
    field_simp
  rw [hlog] at hfixed
  exact hfixed

end StatisticalRL.OnlineRL
