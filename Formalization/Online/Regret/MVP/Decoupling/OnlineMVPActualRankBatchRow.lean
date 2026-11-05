import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.Regret.MVP.MVPUniformSourceDefinitions
import Formalization.Online.Regret.MVP.OnlineMVPStoredClosedForm
import Formalization.Online.Regret.MVP.Optimism.MVPFiniteStackPlanningRow

/-! Actual retained empirical rows agree with the manuscript's dyadic batch
row at every valid visit rank.  This is a pointwise stack/history identity;
it makes no concentration or event assumption. -/
namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpRankBatchStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpRankBatchActionDecidable : DecidableEq Action := Classical.decEq Action

private theorem mvpActualRank_list_slice_ofFn
    {α : Type*} (xs : List α) (start size : ℕ)
    (hbound : start + size ≤ xs.length) :
    (xs.take (start + size)).drop start =
      List.ofFn (fun i : Fin size => xs.get ⟨start + i.val, by omega⟩) := by
  have hlen : ((xs.take (start + size)).drop start).length = size := by
    simp only [List.length_drop, List.length_take]
    omega
  apply List.ext_getElem?'
  intro i hi
  have his : i < size := by simpa [hlen] using hi
  have hiL : i < ((xs.take (start + size)).drop start).length := by
    simpa only [hlen] using his
  have hiR : i < (List.ofFn (fun i : Fin size =>
      xs.get ⟨start + i.val, by omega⟩)).length := by simpa using his
  simp only [List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hiR,
    List.getElem_drop, List.getElem_take, List.getElem_ofFn]
  congr 1

/-- At visit-count rank `u = 2·2^j+i`, the retained planning row is exactly
`batchRow data j`; the bound `u<K` ensures this is a real visit, and every
batch coordinate is in the finite stack. -/
theorem onlineMVPActualPlanningRow_eq_sourceBatchRow_at_rank
    {H K : ℕ} [Nonempty State] (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K * H) (h : Fin H) (s : State) (a : Action)
    (j : Fin (Nat.log2 K)) (i : Fin (2 * 2^j.val))
    (huK : 2 * 2^j.val + i.val < K)
    (hu : onlineVisitCount
      (onlineMVPActualStackRowAt hH initial fallback planner data) n (h, (s, a)) =
        2 * 2^j.val + i.val) :
    onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n h) s a =
      MVPUniformSource.batchRow data j h s a := by
  classical
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let nextAt := onlineMVPActualStackNextAt hH initial fallback planner data
  let r : OnlineMDPRow State Action H := (h, (s, a))
  let history := onlineMVPActualStackHistory hH initial fallback planner data n
  let xs := onlineMVPRowVisitList rowAt nextAt n r
  have hpowlow : 2^(j.val+1) ≤ 2*2^j.val + i.val := by
    have hi := i.isLt
    simp only [pow_succ]
    omega
  have hpowhigh : 2*2^j.val + i.val < 2^(j.val+2) := by
    have hi := i.isLt
    simp only [pow_succ]
    omega
  have hlog : Nat.log2 (2*2^j.val + i.val) = j.val + 1 :=
    onlineMVP_log2_eq_of_dyadic_bounds _ _ hpowlow hpowhigh
  let u := 2*2^j.val + i.val
  have hprofile : sourceMVPProfileIndex u = j.val + 2 := by
    simp [u, sourceMVPProfileIndex, hlog]
  have hstoredCount : onlineMVPStoredCount u = 2^j.val := by
    rw [onlineMVP_storedCount_eq_profile_batch, hprofile]
    simp
  have hstart : onlineMVPSourceBatchStart u = 2^j.val := by
    rw [onlineMVPSourceBatchStart, if_neg (by dsimp [u]; omega),
      onlineMVP_storedCount_closedForm, if_neg (by dsimp [u]; omega), hlog]
    simp
  have hend : onlineMVPSourceBatchEnd u = 2^(j.val+1) := by
    rw [onlineMVPSourceBatchEnd_eq_logPower (n := u) (by dsimp [u]; omega), hlog]
  have hstored :
      (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r = 2^j.val := by
    rw [onlineMVPCommittedPlanningRow_profile_index, hu, hprofile]
    simp
  have hpos : 0 < (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r := by
    rw [hstored]
    positivity
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  have hhistorylen : history.length = n := by
    simpa [history, choose, stream, onlineMVPActualStackHistory] using
      onlineStackHistory_length choose stream n
  have hrowsConsistent : onlineTranscriptRowsConsistent choose history := by
    simpa [choose, history, onlineMVPActualStackHistory] using
      onlineActualStackHistory_rows_consistent choose stream n
  have hrows : ∀ q : Fin history.length, rowAt q.val = (history.get q).1 := by
    intro q
    have hqle : q.val ≤ n := by have := q.isLt; omega
    have htake : history.take q.val = onlineStackHistory choose stream q.val := by
      simpa [history, onlineMVPActualStackHistory, choose, stream] using
        onlineStackHistory_take choose stream n q.val hqle
    calc
      rowAt q.val = choose (onlineStackHistory choose stream q.val) := by
        simp [rowAt, onlineMVPActualStackRowAt, onlineMVPActualStackHistory, choose, stream]
      _ = choose (history.take q.val) := congrArg choose htake.symm
      _ = (history.get q).1 := (hrowsConsistent q).symm
  have hcount : (onlineRowOutcomes history r).length = u := by
    have hcount' := onlineTranscript_rowCount_eq_visitCount history rowAt hrows n
      (by rw [hhistorylen]) r
    have htake : history.take n = history := by
      simpa [hhistorylen] using (List.take_length history)
    rw [htake] at hcount'
    calc
      (onlineRowOutcomes history r).length = onlineVisitCount rowAt n r := hcount'
      _ = u := by simpa [u, rowAt, r] using hu
  have hxs : xs.length = u := by
    have hlist := onlineMVPActualStackHistory_rowVisitList
      hH initial fallback planner data n r
    calc
      xs.length = (onlineRowOutcomes history r).length := by
        simpa [xs, rowAt, nextAt, r, history, onlineMVPActualStackHistory] using
          congrArg List.length hlist
      _ = u := hcount
  have hstartxs : onlineMVPSourceBatchStart xs.length = 2^j.val := by
    simpa [hxs] using hstart
  have hendxs : onlineMVPSourceBatchEnd xs.length = 2^(j.val+1) := by
    simpa [hxs] using hend
  have hbatchShape : onlineMVPSourceBatchList xs =
      List.ofFn (fun q : Fin (2^j.val) =>
        xs.get ⟨2^j.val + q.val, by
          have hq := q.isLt
          rw [hxs]
          dsimp [u]
          omega⟩) := by
    have hbound : 2^j.val + 2^j.val ≤ xs.length := by
      rw [hxs]
      have hi := i.isLt
      omega
    have hpow : 2^j.val + 2^j.val = 2^(j.val+1) := by
      rw [Nat.pow_succ]
      ring
    change (xs.take (onlineMVPSourceBatchEnd xs.length)).drop
      (onlineMVPSourceBatchStart xs.length) = _
    rw [hstartxs, hendxs]
    change (xs.take (2^(j.val+1))).drop (2^j.val) = _
    rw [← hpow]
    exact mvpActualRank_list_slice_ofFn xs (2^j.val) (2^j.val) hbound
  have hbatchData : onlineMVPSourceBatchList xs =
      List.ofFn (fun q : Fin (2^j.val) =>
        data (r, ⟨2^j.val + q.val, by
          have hq := q.isLt
          have hpow : 2^j.val + q.val < 2 * 2^j.val := by
            have h := Nat.add_lt_add_left hq (2^j.val)
            simpa [two_mul] using h
          omega⟩)) := by
    rw [hbatchShape]
    congr 1
    funext q
    have hidx : 2^j.val + q.val < (onlineRowOutcomes history r).length := by
      rw [hcount]
      have hq := q.isLt
      dsimp [u]
      omega
    have hidxxs : 2^j.val + q.val < xs.length := by
      rw [hxs]
      have hq := q.isLt
      dsimp [u]
      omega
    have hrowlist := onlineMVPActualStackHistory_rowVisitList
      hH initial fallback planner data n r
    have hread := onlineMVPActualStackHistory_rowNth_eq_stack
      hH initial fallback planner data n hn r ⟨2^j.val + q.val, hidx⟩
    have hgetD := congrArg (fun ys : List State => ys.getD (2^j.val + q.val) fallback) hrowlist
    have hget : xs.get ⟨2^j.val + q.val, hidxxs⟩ =
        (onlineRowOutcomes history r).get ⟨2^j.val + q.val, hidx⟩ := by
      calc
        xs.get ⟨2^j.val + q.val, hidxxs⟩ = xs.getD (2^j.val + q.val) fallback :=
          (List.getD_eq_get xs fallback ⟨2^j.val + q.val, hidxxs⟩).symm
        _ = (onlineRowOutcomes history r).getD (2^j.val + q.val) fallback := by
          simpa [xs, rowAt, nextAt, r, history, onlineMVPActualStackHistory] using hgetD
        _ = (onlineRowOutcomes history r).get ⟨2^j.val + q.val, hidx⟩ :=
          List.getD_eq_get _ fallback ⟨2^j.val + q.val, hidx⟩
    exact hget.trans hread
  have hrowEmpirical := onlineMVPActualStackPlanningRow_eq_sourceBatch
    hH E initial fallback planner data n h s a hpos
  have hrowEmpirical' :
      onlineObservedPlanningRow (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
        FiniteDistribution.empiricalRow (onlineMVPSourceBatchList xs).length
          (by rw [hbatchData]; simp)
          (fun q => (onlineMVPSourceBatchList xs).get q) := by
    simpa [xs, rowAt, nextAt, r] using hrowEmpirical
  have hlenBatch : (onlineMVPSourceBatchList xs).length = 2^j.val := by
    rw [hbatchData]
    simp
  have hpoint : ∀ q : Fin (2^j.val),
      (onlineMVPSourceBatchList xs).get ⟨q.val, by omega⟩ =
        data (r, ⟨2^j.val + q.val, by
          have hq := q.isLt
          have hpow : 2^j.val + q.val < 2 * 2^j.val := by
            have h := Nat.add_lt_add_left hq (2^j.val)
            simpa [two_mul] using h
          omega⟩) := by
    intro q
    have hgetD := congrArg (fun ys : List State => ys.getD q.val fallback) hbatchData
    calc
      (onlineMVPSourceBatchList xs).get ⟨q.val, by rw [hlenBatch]; exact q.isLt⟩ =
          (onlineMVPSourceBatchList xs).getD q.val fallback :=
        (List.getD_eq_get _ fallback ⟨q.val, by rw [hlenBatch]; exact q.isLt⟩).symm
      _ = (List.ofFn fun q : Fin (2^j.val) =>
          data (r, ⟨2^j.val + q.val, by
            have hq := q.isLt
            have hpow : 2^j.val + q.val < 2 * 2^j.val := by
              have h := Nat.add_lt_add_left hq (2^j.val)
              simpa [two_mul] using h
            omega⟩)).getD q.val fallback := by
          simpa using hgetD
      _ = data (r, ⟨2^j.val + q.val, by
            have hq := q.isLt
            have hpow : 2^j.val + q.val < 2 * 2^j.val := by
              have h := Nat.add_lt_add_left hq (2^j.val)
              simpa [two_mul] using h
            omega⟩) := by simp
  have hemp := mvp_empiricalRow_list_eq_vector
    (onlineMVPSourceBatchList xs) (2^j.val) hlenBatch
    (by rw [hlenBatch]; positivity) (by positivity)
    (fun q : Fin (2^j.val) => data (r, ⟨2^j.val + q.val, by
      have hq := q.isLt
      have hpow : 2^j.val + q.val < 2 * 2^j.val := by
        have h := Nat.add_lt_add_left hq (2^j.val)
        simpa [two_mul] using h
      omega⟩)) hpoint
  have hrowEmpirical'' :
      onlineObservedPlanningRow (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
        FiniteDistribution.empiricalRow (onlineMVPSourceBatchList xs).length
          (by rw [hlenBatch]; positivity)
          (fun q => (onlineMVPSourceBatchList xs).get q) := by
    simpa [xs, rowAt, nextAt, r] using hrowEmpirical
  calc
    onlineObservedPlanningRow (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
        FiniteDistribution.empiricalRow (onlineMVPSourceBatchList xs).length
          (by rw [hlenBatch]; positivity)
          (fun q => (onlineMVPSourceBatchList xs).get q) := hrowEmpirical''
    _ = MVPUniformSource.batchRow data j h s a := by
      simpa [MVPUniformSource.batchRow, MVPUniformSource.batchIndex] using hemp

end StatisticalRL.OnlineRL
