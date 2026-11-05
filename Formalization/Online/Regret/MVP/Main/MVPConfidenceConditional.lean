import Formalization.Online.Regret.MVP.Main.MVPDecouplingConsumer
import Formalization.Online.Regret.MVP.Main.MVPAllocatedBudget
import Formalization.Online.Regret.MVP.Main.MVPLargeMin
import Formalization.Online.Regret.MVP.Optimism.MVPSourceOptimismFinal
import Formalization.Online.Regret.MVP.T5.MVPT5AllKConfidence
import Formalization.Online.Regret.MVP.T6.MVPActualT6SourceFinal

/-! Conditional confidence assembly from an explicit decoupling confidence bound. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpMainConditionalState : MeasurableSpace State := ⊤
local instance mvpMainConditionalSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

theorem mvpMain_large_confidence_of_decoupling_producer
    (H K : ℕ) (hH : 0<H) (hK2 : 2≤K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hlarge : let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      (Fintype.card State : ℝ)*Fintype.card Action*H*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p ≤ K)
    (hdecProb : let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/p)) 4 16
      1-p ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        (mvpActualDecouplingEvent H K hH E fallback p 4 16 I : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)))) :
    let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/p)) 4 16
    1-δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
      {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
        (∑ k : Fin K, mvpActualEpisodeRegret H K hH E sample.1 fallback sample.2 k p 4 16) ≤
          100*max 1 I*min ((K : ℝ)*H) (Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2))} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/p)) 4 16
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let A : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :=
    {sample | mvpHistoryAllStageOptimism (K := K) hH E fallback p 4 16
      (mvpVarianceHistory H K hH E sample.1 fallback sample.2 p 4 16)}
  let B := mvpActualT234Event H K hH E fallback p I
  let C : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := mvpActualDecouplingEvent H K hH E fallback p 4 16 I
  let D : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :=
    {sample | mvpActualT5 H K hH E sample.1 fallback sample.2 p 4 16 ≤
      mvpActualW3 H K hH E sample.1 fallback sample.2 p 4 16 +
      2*H*mvpVarianceT2 H K hH E sample.1 fallback sample.2 p 4 16 +
      Real.sqrt ((H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 p 4 16*I)+K*(H : ℝ)^2*I}
  let F := mvpT6SourceEvent H K hH E fallback p 4 16
  let d : ℝ := (Fintype.card State : ℝ)*Fintype.card Action*H
  have ha : 1-2*d*K*p ≤ μ.real A := by
    simpa [μ,A,planner,p,d,mvpVarianceHistory,mul_assoc] using
      (mvp_sourceOptimismCorrected_holds (State := State) (Action := Action)
        H K hH (by omega) E ρ fallback δ 4 16 hδ hδ1 (by norm_num) (by norm_num))
  have hb : 1-4*(Real.log K/Real.log 2)*p < μ.real B := by
    simpa [μ,B,planner,p,I] using mvpActualT234_source_confidence_K2 H K hH hK2 E ρ fallback δ hδ hδ1.le
  have hc : 1-p ≤ μ.real C := by simpa [μ,C,planner,p,I] using hdecProb
  have he : 1-2*Real.log (K*H)*p ≤ μ.real D := by
    simpa [μ,D,planner,p,I] using mvpActualT5_source_confidence H K hH (by omega) E ρ fallback δ hδ hδ1.le
  have hf : 1-4*d*K*p ≤ μ.real F := by
    simpa [μ,F,planner,p,d,mul_assoc] using mvpActualT6_source_confidence H K hH (by omega) E ρ fallback δ 4 16 hδ hδ1.le (by norm_num) (by norm_num)
  have hinter := mvp_main_five_event_collector μ A B C D F
    (2*d*K*p) (4*(Real.log K/Real.log 2)*p) p (2*Real.log (K*H)*p) (4*d*K*p) ha hb hc he hf
  have hs : 0<Fintype.card State := Fintype.card_pos
  have hact : 0<Fintype.card Action := Fintype.card_pos
  have hbudget := mvp_main_allocated_failure_budget (Fintype.card State) (Fintype.card Action) H K δ hs hact hH hK2 hδ.le
  have hd : (1:ℝ)≤d := by
    have hs1 : (1:ℝ)≤Fintype.card State := by exact_mod_cast hs
    have ha1 : (1:ℝ)≤Fintype.card Action := by exact_mod_cast hact
    have hh1 : (1:ℝ)≤H := by exact_mod_cast hH
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs1 ha1) hh1
  have hI : 1≤I := by
    have hi := mvp_main_iota_ge_log2 (Fintype.card State) (Fintype.card Action) H K δ hs hact hH hK2 hδ hδ1.le
    have hb1 : 1≤Real.log K/Real.log 2 := by
      apply (le_div_iff₀ (Real.log_pos (by norm_num))).2
      simpa only [one_mul] using Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤K by exact_mod_cast hK2)
    exact le_trans hb1 hi
  have hsub : (((A∩B)∩C)∩D)∩F ⊆
      {sample | (∑ k : Fin K, mvpActualEpisodeRegret H K hH E sample.1 fallback sample.2 k p 4 16) ≤
        100*max 1 I*min ((K : ℝ)*H) (Real.sqrt (d*K*(H : ℝ)^2))} := by
    intro sample hsamp
    have hr := mvpActualRegret_large_of_decoupling H K hH hK2 E sample.1 fallback sample.2 δ hδ hδ1.le
      hlarge hsamp.1.1.1.1 hsamp.1.1.1.2 hsamp.1.1.2 hsamp.1.2 hsamp.2
    exact mvp_main_large_min_rate d H K I _ hd (by exact_mod_cast hH) hI hlarge hr
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hbudget' : 2*d*K*p + 4*(Real.log K/Real.log 2)*p + p +
      2*Real.log (K*H)*p + 4*d*K*p ≤ δ := by
    dsimp [d,p]
    convert hbudget using 1 <;> push_cast <;> ring
  exact le_trans (by linarith [hbudget']) (le_of_lt (lt_of_lt_of_le hinter hmono))
end StatisticalRL.OnlineRL
