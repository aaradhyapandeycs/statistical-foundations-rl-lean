import Formalization.Online.Regret.MVP.Optimism.MVPFiniteStackBatch
import Formalization.Online.Regret.MVP.Optimism.MVPBackwardOptimism

/-! Same-data identification of the actual MVP planning row and its
deterministic finite-stack batch. This is an intermediate pathwise bridge. -/
namespace StatisticalRL.OnlineRL
open StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
noncomputable local instance mvpStackStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpStackActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Compare list and vector empirical rows after generalizing their common
length, so no dependent rewrite traverses a `Fin` binder. -/
theorem mvp_empiricalRow_list_eq_vector {α : Type*} [Fintype α]
    (ys : List α) (N : ℕ) (hsize : ys.length = N)
    (hy : 0 < ys.length) (hN : 0 < N) (v : Fin N → α)
    (hpoint : ∀ i : Fin N, ys.get ⟨i.val, by omega⟩ = v i) :
    FiniteDistribution.empiricalRow ys.length hy (fun i => ys.get i) =
      FiniteDistribution.empiricalRow N hN v := by
  subst N
  congr 1
  funext i
  exact hpoint i

theorem mvp_actualPlanningRow_eq_finiteStackBatch {H K : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (choose : List ((Fin H × State × Action) × State) → Fin H × State × Action)
    (fallback : State) (data : (Fin H × State × Action) × Fin K → State)
    (t : ℕ) (h : Fin H) (s : State) (a : Action)
    (hcount : (onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) t) (h,s,a)).length ≤ K)
    (hlarge : 3 ≤ ((onlineMVPActualPlanningStage E
      (mvpStackRowAt choose (onlineFiniteStackExtend K fallback data))
      (mvpStackNextAt choose (onlineFiniteStackExtend K fallback data)) t h).observations s a).length) :
    let xs := onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) t) (h,s,a)
    let m := onlineMVPStoredCount xs.length
    ∃ (hm : 0 < m) (hfit : 2*m ≤ K),
      onlineObservedPlanningRow (onlineMVPActualPlanningStage E
        (mvpStackRowAt choose (onlineFiniteStackExtend K fallback data))
        (mvpStackNextAt choose (onlineFiniteStackExtend K fallback data)) t h) s a =
      FiniteDistribution.empiricalRow m hm
        (mvpBatchSlice K m hfit (fun i => data ((h,s,a),i))) := by
  dsimp only
  let stream := onlineFiniteStackExtend K fallback data
  let xs := onlineRowOutcomes (onlineStackHistory choose stream t) (h,s,a)
  have hxs : onlineMVPRowVisitList (mvpStackRowAt choose stream)
      (mvpStackNextAt choose stream) t (h,s,a) = xs :=
    mvpStackRowVisitList_eq_observed choose stream t (h,s,a)
  have hbatch : 3 ≤ (onlineMVPSourceBatchList xs).length := by
    simpa [onlineMVPActualPlanningStage, stream, xs, hxs] using hlarge
  have hm3 : 3 ≤ onlineMVPStoredCount xs.length := by
    simpa only [onlineMVPSourceBatchList_length] using hbatch
  have hm : 0 < onlineMVPStoredCount xs.length := by omega
  have hx : 2 ≤ xs.length := by
    by_contra hx
    have hc := onlineMVP_storedCount_closedForm xs.length
    simp [show xs.length < 2 by omega] at hc
    omega
  have hfit : 2 * onlineMVPStoredCount xs.length ≤ K :=
    (mvp_sourceBatch_dyadic_fit xs hx).trans hcount
  refine ⟨hm, hfit, ?_⟩
  have hp : 0 < ((onlineMVPActualPlanningStage E (mvpStackRowAt choose stream)
      (mvpStackNextAt choose stream) t h).observations s a).length := by simpa [stream] using (show 0 < _ from by omega)
  rw [onlineObservedPlanningRow_positive _ _ _ hp]
  have hv : (fun j : Fin (onlineMVPStoredCount xs.length) =>
      (onlineMVPSourceBatchList xs).get ⟨j.val, by rw [onlineMVPSourceBatchList_length]; exact j.isLt⟩) =
      mvpBatchSlice K (onlineMVPStoredCount xs.length) hfit (fun i => data ((h,s,a),i)) := by
    funext j
    simpa [mvpBatchSlice, xs, stream] using
      mvp_retainedBatch_eq_finiteStackSlice choose K fallback data t (h,s,a) hx hcount j
  let ys := (onlineMVPActualPlanningStage E (mvpStackRowAt choose stream)
    (mvpStackNextAt choose stream) t h).observations s a
  have hys : ys = onlineMVPSourceBatchList xs := by
    change onlineMVPSourceBatchList (onlineMVPRowVisitList _ _ _ _) = _
    rw [hxs]
  have hsize : ys.length = onlineMVPStoredCount xs.length := by
    rw [hys, onlineMVPSourceBatchList_length]
  apply mvp_empiricalRow_list_eq_vector ys _ hsize hp hm
  intro i
  have hi : i.val < ys.length := by omega
  have hb : i.val < (onlineMVPSourceBatchList xs).length := by
    rw [onlineMVPSourceBatchList_length]
    exact i.isLt
  have heq := congrArg (fun z : List State => z[i.val]?) hys
  have hiEq : ys.get ⟨i.val, hi⟩ = (onlineMVPSourceBatchList xs).get ⟨i.val, hb⟩ := by
    apply Option.some.inj
    simpa [List.get_eq_getElem, hi, hb] using heq
  exact hiEq.trans (congrFun hv i)

end StatisticalRL.OnlineRL
