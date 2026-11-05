import Formalization.Online.Regret.MVP.Main.MVPConfidenceConditional
import Formalization.Online.Regret.MVP.Main.MVPActualSmallRegime
import Formalization.Online.Regret.MVP.Main.MVPExpandedRegret

/-! All-K confidence assembly from an explicit decoupling confidence bound. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpMainAllKState : MeasurableSpace State := ⊤
local instance mvpMainAllKSample (H K : ℕ) : MeasurableSpace
  ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

theorem mvpMain_allK_expanded_confidence_of_decoupling_producer
    (H K : ℕ) (hH : 0<H) (hK : 0<K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hdecProb : 2≤K → ((Fintype.card State : ℝ)*Fintype.card Action*H*(Real.log K/Real.log 2) ≤ K) → let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/p)) 4 16
      1-p ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        (mvpActualDecouplingEvent H K hH E fallback p 4 16 I : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)))) :
    let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/p)) 4 16
    1-δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
      {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
        (∑ k : Fin K,
          (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
          DecisionStage.trajectoryValue
            (List.ofFn (fun h : Fin H => (E h).withPolicy (fun s => EnvironmentStage.pointMass
              (planner ((mvpVarianceHistory H K hH E sample.1 fallback sample.2 p 4 16).take (k.val*H)) h s))))
            (sample.1 k))) ≤
          100*max 1 I*min (Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*(H : ℝ)^3*K)) ((H : ℝ)*K)} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let p := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K p
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/p)) 4 16
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let good : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :=
    {sample | (∑ k : Fin K, mvpActualEpisodeRegret H K hH E sample.1 fallback sample.2 k p 4 16) ≤
      100*max 1 I*min ((K : ℝ)*H) (Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2))}
  have hgood : 1-δ ≤ μ.real good := by
    by_cases hsmall : (K : ℝ) ≤ (Fintype.card State : ℝ)*Fintype.card Action*H*max 1 I
    · have hall : good = Set.univ := by
        apply Set.eq_univ_of_forall
        intro sample
        exact mvpActualRegret_small_regime H K hH E sample.1 fallback sample.2 p hsmall
      rw [hall, probReal_univ]
      linarith
    · have hK2 : 2≤K := by
        by_contra hn
        have hK1 : K=1 := by omega
        subst K
        have hs : (1:ℝ)≤Fintype.card State := by exact_mod_cast Fintype.card_pos (α := State)
        have ha : (1:ℝ)≤Fintype.card Action := by exact_mod_cast Fintype.card_pos (α := Action)
        have hh : (1:ℝ)≤H := by exact_mod_cast hH
        have hd : (1:ℝ)≤(Fintype.card State:ℝ)*Fintype.card Action*H :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs ha) hh
        have := mul_le_mul hd (le_max_left (1:ℝ) I) (by norm_num) (by positivity : (0:ℝ)≤(Fintype.card State:ℝ)*Fintype.card Action*H)
        exact hsmall (by simpa using this)
      have hi0 := mvp_main_iota_ge_log2 (Fintype.card State) (Fintype.card Action) H K δ
        (Fintype.card_pos) (Fintype.card_pos) hH hK2 hδ hδ1.le
      have hb1 : 1≤Real.log K/Real.log 2 := by
        apply (le_div_iff₀ (Real.log_pos (by norm_num))).2
        simpa only [one_mul] using Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤K by exact_mod_cast hK2)
      have hi : 1≤I := le_trans hb1 hi0
      have hlarge : (Fintype.card State : ℝ)*Fintype.card Action*H*I≤K := by
        simpa [max_eq_right hi] using le_of_not_ge hsmall
      have hd0 : 0≤(Fintype.card State : ℝ)*Fintype.card Action*H := by positivity
      have heligible : (Fintype.card State : ℝ)*Fintype.card Action*H*(Real.log K/Real.log 2) ≤ K :=
        le_trans (mul_le_mul_of_nonneg_left hi0 hd0) hlarge
      simpa [μ,good,planner,p,I] using
        mvpMain_large_confidence_of_decoupling_producer H K hH hK2 E ρ fallback δ hδ hδ1 hlarge (hdecProb hK2 heligible)
  have heq : {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
        (∑ k : Fin K,
          (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
          DecisionStage.trajectoryValue
            (List.ofFn (fun h : Fin H => (E h).withPolicy (fun s => EnvironmentStage.pointMass
              (planner ((mvpVarianceHistory H K hH E sample.1 fallback sample.2 p 4 16).take (k.val*H)) h s)))) (sample.1 k))) ≤
          100*max 1 I*min (Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*(H : ℝ)^3*K)) ((H : ℝ)*K)} = good := by
    ext sample
    have hsumeq : (∑ k : Fin K, mvpActualEpisodeRegret H K hH E sample.1 fallback sample.2 k p 4 16) =
        ∑ k : Fin K, (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
          DecisionStage.trajectoryValue (List.ofFn (fun h : Fin H => (E h).withPolicy (fun s => EnvironmentStage.pointMass
            (planner ((mvpVarianceHistory H K hH E sample.1 fallback sample.2 p 4 16).take (k.val*H)) h s)))) (sample.1 k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact mvpActualEpisodeRegret_eq_expanded H K hH E sample.1 fallback sample.2 k p 4 16
    have hrad : (Fintype.card State : ℝ)*Fintype.card Action*(H : ℝ)^3*K =
      (Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2 := by ring
    change (∑ k : Fin K, (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
      DecisionStage.trajectoryValue (List.ofFn (fun h : Fin H => (E h).withPolicy (fun s => EnvironmentStage.pointMass
        (planner ((mvpVarianceHistory H K hH E sample.1 fallback sample.2 p 4 16).take (k.val*H)) h s)))) (sample.1 k))) ≤ _ ↔ _
    rw [← hsumeq, hrad, min_comm, mul_comm (H : ℝ) K]
    rfl
  change 1-δ ≤ μ.real _
  rw [heq]
  exact hgood
end StatisticalRL.OnlineRL
