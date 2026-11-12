import Formalization.Online.Regret.MVP.Optimism.MVPFiniteStackPlanningRow
import Formalization.Online.Regret.MVP.Optimism.MVPBatchBonus
import Formalization.Online.SourceOptimism.GreedySequentialBellmanOptimism
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Intermediate actual-stack event transfer. The count bound is an explicit
pathwise premise here, to be derived from stage-tagged episode history by the
later source-law consumer; it is not a source confidence assumption. -/
namespace StatisticalRL.OnlineRL
open StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
noncomputable local instance mvpEventStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance mvpEventActionEq : DecidableEq Action := Classical.decEq Action

theorem mvp_batchEvent_implies_actualCertificates {H K : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (choose : List ((Fin H × State × Action) × State) → Fin H × State × Action)
    (fallback : State) (data : (Fin H × State × Action) × Fin K → State)
    (δ c₁ c₂ : ℝ)
    (hcount : ∀ k : Fin K, ∀ r,
      (onlineRowOutcomes (onlineStackHistory choose
        (onlineFiniteStackExtend K fallback data) (k.val*H)) r).length ≤ K)
    (hevent : ∀ r n, 3 ≤ n → n < K →
      data ∈ mvpBatchBonusGood E (onlineTrueSuffixRowFamily E) K δ c₁ c₂ r n) :
    onlineMVPObservedBatchCertificates E K
      (mvpStackRowAt choose (onlineFiniteStackExtend K fallback data))
      (mvpStackNextAt choose (onlineFiniteStackExtend K fallback data)) δ c₁ c₂ := by
  intro k h s a
  dsimp only
  intro hlarge U hU
  let stream := onlineFiniteStackExtend K fallback data
  let xs := onlineRowOutcomes (onlineStackHistory choose stream (k.val*H)) (h,s,a)
  have hxs := mvpStackRowVisitList_eq_observed choose stream (k.val*H) (h,s,a)
  have hbatch : 3 ≤ (onlineMVPSourceBatchList xs).length := by
    simpa [onlineMVPActualPlanningStage, stream, xs, hxs] using hlarge
  have hm3 : 3 ≤ onlineMVPStoredCount xs.length := by
    simpa only [onlineMVPSourceBatchList_length] using hbatch
  have hx : 2 ≤ xs.length := by
    by_contra hx
    have hc := onlineMVP_storedCount_closedForm xs.length
    simp [show xs.length < 2 by omega] at hc
    omega
  have hfit : 2*onlineMVPStoredCount xs.length ≤ K :=
    (mvp_sourceBatch_dyadic_fit xs hx).trans (hcount k (h,s,a))
  have hm : 0 < onlineMVPStoredCount xs.length := by omega
  have hlt : onlineMVPStoredCount xs.length < K := by omega
  have hg := hevent (h,s,a) (onlineMVPStoredCount xs.length) hm3 hlt
  simp only [mvpBatchBonusGood, dif_pos (show 0 < onlineMVPStoredCount xs.length ∧ 2 * onlineMVPStoredCount xs.length ≤ K from ⟨hm,hfit⟩), Set.mem_setOf_eq] at hg
  obtain ⟨hm', hfit', hrow⟩ := mvp_actualPlanningRow_eq_finiteStackBatch
    E choose fallback data (k.val*H) h s a (hcount k (h,s,a)) hlarge
  have hc := hg U (by simpa [onlineTrueSuffixRowFamily] using hU)
  rw [hrow]
  simpa [onlineTrueSuffixRowFamily, onlineMVPActualPlanningStage, stream, xs, hxs,
    onlineMVPSourceBatchList_length] using hc

end StatisticalRL.OnlineRL
