import Formalization.Online.Regret.MVP.Optimism.MVPOptimismLawTransport
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualPlanningAdapter

/-! Corrected actual sequential MVP optimism: the table bridge is proved
pathwise from Data's completed-history adapter, not assumed. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpFinalStateMeasurable : MeasurableSpace State := ⊤
local instance mvpFinalTranscriptMeasurable (H K : ℕ) : MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance mvpFinalAtomMeasurable (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State n) := ⊤

theorem mvp_sourceOptimismCorrected_holds : MVPSourceOptimismCorrected (State := State) (Action := Action) := by
  classical
  intro H K hH hK E ρ fallback δ c₁ c₂ hδ hδ1 hc₁ hc₂
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  have hp := mvp_stackOptimism_to_sequential hH hK E ρ fallback δ c₁ c₂ hδ hδ1.le hc₁ hc₂
    (by
      intro initial data hs k h
      let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
      have hk : k.val*H ≤ K*H := Nat.mul_le_mul_right H (Nat.le_of_lt k.isLt)
      have ht := onlineStackHistory_take (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) (K*H) (k.val*H) hk
      have ht' : (onlineMVPActualStackHistory hH initial fallback planner data (K*H)).take (k.val*H) =
          onlineMVPActualStackHistory hH initial fallback planner data (k.val*H) := ht
      have htable := onlineMVPHistoryPlanningStages_actualStack_eq hH E initial fallback planner data (k.val*H)
      dsimp [planner, δp] at ht' htable
      have hkh := hs k h
      simpa only [mvpHistoryAllStageOptimism, ht', htable, onlineMVPPlanningStages] using hkh)
  exact hp.le
end StatisticalRL.OnlineRL
