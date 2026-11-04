import Formalization.Online.Regret.MVP.Optimism.MVPBatchEventTransfer
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.SourceOptimism.GreedySequentialBellmanOptimism

/-! Actual retained-batch stack optimism on the simultaneous batch event.
The event probability and transcript-law transfer are separate obligations. -/
namespace StatisticalRL.OnlineRL
open StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
noncomputable local instance mvpStackOptStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance mvpStackOptActionEq : DecidableEq Action := Classical.decEq Action

theorem mvp_sourceStack_optimistic_of_batchEvent {H K : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hevent : ∀ r n, 3 ≤ n → n < K →
      data ∈ mvpBatchBonusGood E (onlineTrueSuffixRowFamily E) K δ c₁ c₂ r n) :
    ∀ (k : Fin K) (h : Fin H),
      (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
        onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
          (onlineMVPPlanningStages E
            (onlineMVPActualStackRowAt hH initial fallback
              (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) data)
            (onlineMVPActualStackNextAt hH initial fallback
              (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) data)
            (k.val*H)) h.val s) ∧
      (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
        onlineCappedBackwardQAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
          (onlineMVPPlanningStages E
            (onlineMVPActualStackRowAt hH initial fallback
              (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) data)
            (onlineMVPActualStackNextAt hH initial fallback
              (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) data)
            (k.val*H)) h.val s a) := by
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  have hcount : ∀ k : Fin K, ∀ r,
      (onlineRowOutcomes (onlineStackHistory choose
        (onlineFiniteStackExtend K fallback data) (k.val*H)) r).length ≤ K := by
    intro k r
    exact onlineMVPActualStackHistory_rowCount_le_K hH initial fallback planner data
      (k.val*H) (Nat.mul_le_mul_right H (Nat.le_of_lt k.isLt)) r
  have hcert := mvp_batchEvent_implies_actualCertificates E choose fallback data δ c₁ c₂ hcount hevent
  have hL : 1 ≤ Real.log (1/δ) := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  intro k h
  exact onlineMVPBatchCertificates_imply_optimism E
    (mvpStackRowAt choose (onlineFiniteStackExtend K fallback data))
    (mvpStackNextAt choose (onlineFiniteStackExtend K fallback data))
    δ c₁ c₂ hL hc₁ hc₂ hcert k h

end StatisticalRL.OnlineRL
