import Formalization.Online.Regret.T5.OnlineT5ActualBound
import Formalization.Online.Regret.T8.OnlineT8SourceConfidence
import Formalization.Online.Regret.PolicyVariance.OnlineT6PolicyConfidence
import Formalization.Online.Regret.Gap.OnlineT6DifferenceActualBound
import Formalization.Online.Regret.Gap.OnlineJ1SourceConfidence
import Formalization.Online.Regret.T0.OnlineT0ActualConfidence
import Formalization.Online.Regret.Algebra.OnlineT56ConfidenceAlgebra

/-! Conditional actual-law T5/T6 joint source bounds. The sole confidence
premise is the actual uniform T0 and optimism event; it is not yet discharged
here by the masked-T3 family. No W3 confidence event or T2 estimate is used. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance jointState : MeasurableSpace State := ⊤
noncomputable local instance jointSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

noncomputable def onlineActualT56JointEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample |
    onlineActualT5 H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ h k) +
      2 * (H : ℝ) * onlineActualT2 H K hH E sample.1 fallback sample.2 δ c₁ c₂ +
      2 * (K : ℝ) * (H : ℝ)^2 +
      Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
      5 * (H : ℝ)^2 * Real.log (1 / δ) ∧
    onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      (K : ℝ) * (H : ℝ)^2 + Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ)) ∧
    onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      2 * (H : ℝ)^2 * onlineActualT0SourceUpper H K hH E fallback sample δ c₁ c₂ +
      18 * (H : ℝ)^2 * Real.log (1 / δ)}

theorem onlineActualT56_joint_confidence_of_T0
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hT0prob :
      let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
      1 - 9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
          (onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂)) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 14 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT56JointEvent H K hH E fallback δ c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let T0 := onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂
  let T8 : Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    {sample | |onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
      Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) + 5 * (H : ℝ)^2 * Real.log (1 / δ)}
  let Low : Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    {sample | onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      (K : ℝ) * (H : ℝ)^2 + Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ))}
  let J : Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2) →
      |onlineActualJ1 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
        Real.sqrt (8 * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
          5 * (H : ℝ) * Real.log (1 / δ)}
  have hn : 2 ≤ K * H := hK.trans (Nat.le_mul_of_pos_right K hH)
  have hp8 := onlineActualT8_source_confidence H K hH hn E ρ fallback δ c₁ c₂ hδ hδsmall (by linarith) ((sq_nonneg c₁).trans hc₂)
  have hpJ := onlineActualJ1_source_confidence_conditional H K hH hn E ρ fallback δ c₁ c₂ hδ hδsmall (by linarith) ((sq_nonneg c₁).trans hc₂)
  have hpL := onlineActualT6Policy_confidence_strict H K hH (by omega) E ρ fallback δ c₁ c₂ hδ (by linarith)
  have hp01 := onlineTwoEvent_confidence_strict μ T8 T0 (2 * (Nat.log2 (K * H) : ℝ) * δ)
    (9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ) hp8 hT0prob
  have hp02 := onlineTwoEvent_confidence_strict μ J (T8 ∩ T0) (2 * (Nat.log2 (K * H) : ℝ) * δ)
    (2 * (Nat.log2 (K * H) : ℝ) * δ + 9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ) hpJ hp01
  have hp03 := onlineTwoEvent_confidence_strict μ Low (J ∩ (T8 ∩ T0)) (2 * δ)
    (2 * (Nat.log2 (K * H) : ℝ) * δ + (2 * (Nat.log2 (K * H) : ℝ) * δ +
      9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ)) (le_of_lt hpL) hp02
  have hsub : Low ∩ (J ∩ (T8 ∩ T0)) ⊆ onlineActualT56JointEvent H K hH E fallback δ c₁ c₂ := by
    intro sample hs
    have hopt := hs.2.2.2.1
    have hstage := hs.2.2.2.2
    have hbound5 := onlineActualT5_le_W3_T8_T2 H K hH E sample.1 fallback sample.2 δ c₁ c₂ hδ
      (by linarith) (by linarith) ((sq_nonneg c₁).trans hc₂)
    have hbound6 := onlineActualT6Difference_le_stagewiseT0_of_J1 H K hH E sample.1 fallback sample.2 δ c₁ c₂
      (onlineActualT0SourceUpper H K hH E fallback sample δ c₁ c₂) hδ (by linarith) (by linarith)
      ((sq_nonneg c₁).trans hc₂) hopt hstage (hs.2.1 hopt)
    refine ⟨?_, hs.1, hbound6⟩
    have h8abs : |onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
        Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
          5 * (H : ℝ)^2 * Real.log (1 / δ) := hs.2.2.1
    have h8 := (le_abs_self _).trans h8abs
    linarith
  have hm := measureReal_mono (μ := μ) hsub (by simp)
  have hnlog := onlineT56_two_natLog2_le (K * H)
  have hN : (2 : ℝ) ≤ K * H := by exact_mod_cast hn
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos (α := State)
  have hA : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos (α := Action)
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hM : (1 : ℝ) ≤ (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H := by
    have hs2 : (1 : ℝ) ≤ (Fintype.card State : ℝ)^2 := one_le_pow₀ hS
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs2 hA) hHr
  have hlog : 2 * (Nat.log2 (K * H) : ℝ) ≤ (K : ℝ) * H := by exact_mod_cast hnlog
  have hcost : 4 * (Nat.log2 (K * H) : ℝ) + 2 ≤
      5 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K := by
    have hm1 := mul_le_mul_of_nonneg_right hM (show 0 ≤ (K : ℝ) * H by positivity)
    linarith only [hm1, hN, hlog]
  have hcostδ := mul_le_mul_of_nonneg_right hcost (le_of_lt hδ)
  change 1 - 14 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ < μ.real _
  linarith only [hp03, hm, hcostδ]
end StatisticalRL.OnlineRL
