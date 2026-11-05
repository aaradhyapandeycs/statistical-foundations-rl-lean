import Formalization.Online.Regret.MVP.Main.MVPAllKConditional
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualDecouplingSourceConfidence

/-! Unconditional actual-law confidence for the corrected MVP regret bound. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open StatisticalRL.OnlineRL.MVPProfile
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpFinalSourceState : MeasurableSpace State := ⊤
local instance mvpFinalSourceSample (H K : ℕ) : MeasurableSpace
  ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

theorem mvpMain_allK_expanded_source_confidence
    (H K : ℕ) (hH : 0<H) (hK : 0<K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
 :
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
  apply mvpMain_allK_expanded_confidence_of_decoupling_producer
    H K hH hK E ρ fallback δ hδ hδ1
  intro hK2 hbudget
  have hbudget' : (K : ℝ) ≥
      (Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K := by
    simpa [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, logTwoReal,
      mul_assoc, mul_left_comm, mul_comm] using hbudget
  have h := mvp_actualDecouplingEvent_sourceConfidence H K hH (by omega)
    E ρ fallback δ 4 16 hδ hδ1.le (by norm_num) (by norm_num) hbudget'
  simpa [onlineW1SourceIota, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    mul_assoc, mul_left_comm, mul_comm] using h.le
end StatisticalRL.OnlineRL
