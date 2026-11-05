import Formalization.Online.Regret.MVP.T34.MVPActualT3Peel
import Formalization.Online.Regret.MVP.T6.MVPActualT8SourceRadius

/-! Source-radius form of the actual MVP T3 concentration estimate. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT3TailState : MeasurableSpace State := ⊤
noncomputable local instance mvpT3TailSample (H K : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤
theorem mvpT3_independent_tail_source_radius_probability
    (H K j : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H)
    (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ δ' : ℝ)
    (hLplanner : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hδ' : 0 < δ') (hδsmall : δ' ≤ 1 / 100)
    (hj : j = Nat.log2 (K * H)) (hbranch : 2 * j * δ' < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    1 - 2 * j * δ' ≤ μ.real
      (onlineFreedmanSourceRadiusSet μ ℱ
        (mvpT3PaddedY H K hH E fallback planner L c₁ c₂) (K * H) ((H : ℝ)) (Real.log (1 / δ'))) := by
  classical
  dsimp
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := mvpT3PaddedY H K hH E fallback planner L c₁ c₂
  have hjpos : 0 < j := by
    rw [hj]
    exact (onlineT3_natLog2_ratio_bounds (K * H) hN).1
  let δF : ℝ := 2 * j * δ'
  have hδF : 0 < δF := by dsimp [δF]; positivity
  have hδF1 : δF < 1 := by simpa [δF] using hbranch
  have hL : 2 ≤ Real.log (1 / δ') :=
    onlineT3_sourceLog_ge_two δ' hδ' hδsmall
  have hL0 : 0 ≤ Real.log (1 / δ') := le_trans (by norm_num) hL
  have hfixedRaw := mvpT3Freedman_peeled_integer H K j hH E ρ fallback planner
    L c₁ c₂ δ' hLplanner hc₁ hc₂ hjpos hδ' hbranch
  have hfixed : 1 - δF ≤ μ.real
      (onlineFreedmanPeeledRadiusSet μ ℱ X (K * H) ((H : ℝ))
        ((K : ℝ) * (H : ℝ)^3) j (Real.log (1 / δ'))) := by
    change 1 - 2 * j * δ' ≤ μ.real {sample | _} at hfixedRaw
    simpa [δF, onlineFreedmanPeeledRadiusSet, μ, ℱ, X] using hfixedRaw
  have hvar := predictableSecondMomentSum_nonneg μ ℱ X (K * H)
  let N := K * H
  let q : ℝ := (N : ℝ) / (2 : ℝ)^j
  have hq := onlineT3_natLog2_ratio_bounds N hN
  dsimp [N] at hq
  rw [← hj] at hq
  rcases hq with ⟨_, hqone, hqtwo⟩
  have hq0 : 0 ≤ q := le_trans (by norm_num) hqone
  have hpow : 0 < (2 : ℝ)^j := by positivity
  have hσq : ((K : ℝ) * (H : ℝ)^3) / (2 : ℝ)^j = q * ((H : ℝ))^2 := by
    dsimp [q, N]
    push_cast
    field_simp
    <;> ring
  have hprob := onlineFreedman_peeledProbability_le_source μ ℱ X (K * H)
    ((H : ℝ)) ((K : ℝ) * (H : ℝ)^3) q (Real.log (1 / δ')) δF j
    hvar (by positivity) hσq hq0 (le_of_lt hqtwo) hL hfixed
  change 1 - 2 * j * δ' ≤ μ.real
    (onlineFreedmanSourceRadiusSet μ ℱ X (K * H) ((H : ℝ)) (Real.log (1 / δ')))
  exact hprob

end StatisticalRL.OnlineRL
