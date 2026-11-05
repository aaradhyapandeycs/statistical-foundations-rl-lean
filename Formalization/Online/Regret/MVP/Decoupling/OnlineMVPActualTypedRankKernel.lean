import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.Regret.MVP.Model.OnlineMVPCommittedModel
import Formalization.Online.Regret.MVP.MVPUniformSourceDefinitions
import Formalization.Online.Regret.MVP.OnlineMVPStoredClosedForm
import Formalization.Online.Regret.MVP.OnlineMVPDyadicTrigger
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualRankBatchRow
import Formalization.Online.Regret.MVP.Decoupling.MVPVisitRankKernel

/-! The deployed actual planning row is represented by the finite, typed
visit-rank kernel: uniform initialization at count zero, the first sample at
count one, and the source dyadic batch thereafter. The prefix bound `u<K` is
an explicit input here; callers at pre-episode times derive it from the
stage-clock visit bound. -/
namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPUniformSource
open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpTypedRankStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpTypedRankActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The first-sample row in the typed source representation. -/
noncomputable def onlineMVPActualFirstVisitRow {H K : ℕ}
    (data : OnlineMDPRow State Action H × Fin K → State)
    (r : OnlineMDPRow State Action H) (hK : 0 < K) : FiniteDistribution State :=
  FiniteDistribution.empiricalRow 1 (by omega)
    (fun _ : Fin 1 => data (r, ⟨0, hK⟩))

/-- At every valid actual visit rank, the observed planning row equals the
rank-indexed typed source kernel. The strict `u<K` premise guarantees the
rank is represented by `Fin K`; it is derivable for all pre-episode rows. -/
theorem onlineMVPActualPlanningRow_eq_typedVisitRankKernel
    {H K : ℕ} [Nonempty State] (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K * H) (h : Fin H) (s : State) (a : Action)
    (huK : onlineVisitCount
      (onlineMVPActualStackRowAt hH initial fallback planner data) n (h, (s, a)) < K) :
    let u := onlineVisitCount
      (onlineMVPActualStackRowAt hH initial fallback planner data) n (h, (s, a))
    onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n h) s a =
      mvp_visitRankKernel K onlineUniformInitialRow
        (onlineMVPActualFirstVisitRow data (h, (s, a)) (by omega))
        (fun j => MVPUniformSource.batchRow data j h s a) ⟨u, huK⟩ := by
  classical
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let nextAt := onlineMVPActualStackNextAt hH initial fallback planner data
  let r : OnlineMDPRow State Action H := (h, (s, a))
  let u : ℕ := onlineVisitCount rowAt n r
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  let history := onlineMVPActualStackHistory hH initial fallback planner data n
  let xs := onlineMVPRowVisitList rowAt nextAt n r
  change onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
    mvp_visitRankKernel K onlineUniformInitialRow
      (onlineMVPActualFirstVisitRow data r (by omega))
      (fun j => MVPUniformSource.batchRow data j h s a) ⟨u, huK⟩
  have hcount : onlineVisitCount rowAt n r = u := rfl
  have hhistorylen : history.length = n := by
    simpa [history, onlineMVPActualStackHistory, choose, stream] using
      onlineStackHistory_length choose stream n
  have hrowsConsistent : onlineTranscriptRowsConsistent choose history := by
    simpa [history, onlineMVPActualStackHistory] using
      onlineActualStackHistory_rows_consistent choose stream n
  have hrows : ∀ q : Fin history.length, rowAt q.val = (history.get q).1 := by
    intro q
    have hqle : q.val ≤ n := by rw [← hhistorylen]; exact q.isLt.le
    have htake : history.take q.val = onlineStackHistory choose stream q.val := by
      simpa [history, onlineMVPActualStackHistory] using
        onlineStackHistory_take choose stream n q.val hqle
    calc
      rowAt q.val = choose (onlineStackHistory choose stream q.val) := by
        change choose (onlineStackHistory choose stream q.val) = _
        rfl
      _ = choose (history.take q.val) := congrArg choose htake.symm
      _ = (history.get q).1 := (hrowsConsistent q).symm
  have hrowCount : (onlineRowOutcomes history r).length = u := by
    have hc := onlineTranscript_rowCount_eq_visitCount history rowAt hrows n
      (by rw [hhistorylen]) r
    have htake : history.take n = history := by
      simpa [hhistorylen] using (List.take_length history)
    rw [htake] at hc
    calc
      (onlineRowOutcomes history r).length = onlineVisitCount rowAt n r := hc
      _ = u := hcount
  have hxsLength : xs.length = u := by
    have hlist := onlineMVPActualStackHistory_rowVisitList
      hH initial fallback planner data n r
    calc
      xs.length = (onlineRowOutcomes history r).length := by
        simpa [xs, rowAt, nextAt, r, history, onlineMVPActualStackHistory] using
          congrArg List.length hlist
      _ = u := hrowCount
  by_cases hzero : u = 0
  · have hstored : (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r = 0 := by
      have hs := onlineMVPCommittedPlanningRow_profile_index rowAt nextAt n r
      rw [hcount, hzero] at hs
      simpa [sourceMVPProfileIndex] using hs
    have hrow := onlineMVPActualStackPlanningRow_eq_uniform_of_zero
      hH E initial fallback planner data n h s a hstored
    have huniform : (onlineMVPUniformDistribution : FiniteDistribution State) =
        onlineUniformInitialRow := by
      apply onlineMVP_finiteDistribution_ext (Ω := State)
      intro x
      simp [onlineMVPUniformDistribution, onlineUniformInitialRow]
    simpa [mvp_visitRankKernel, u, hzero, huniform] using hrow
  · by_cases hone : u = 1
    · have hstored : (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r = 1 := by
        have hs := onlineMVPCommittedPlanningRow_profile_index rowAt nextAt n r
        rw [hcount, hone] at hs
        simpa [sourceMVPProfileIndex] using hs
      have hpos : 0 < (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r := by
        rw [hstored]
        omega
      have hrowlist := onlineMVPActualStackHistory_rowVisitList
        hH initial fallback planner data n r
      have hfirstGet : xs.get ⟨0, by rw [hxsLength, hone]; omega⟩ =
          data (r, ⟨0, by omega⟩) := by
        have hread := onlineMVPActualStackHistory_rowNth_eq_stack
          hH initial fallback planner data n hn r ⟨0, by rw [hrowCount, hone]; omega⟩
        have hgetD := congrArg (fun ys : List State => ys.getD 0 fallback) hrowlist
        calc
          xs.get ⟨0, by rw [hxsLength, hone]; omega⟩ = xs.getD 0 fallback :=
            (List.getD_eq_get xs fallback ⟨0, by rw [hxsLength, hone]; omega⟩).symm
          _ = (onlineRowOutcomes history r).getD 0 fallback := by
            simpa [xs, rowAt, nextAt, r, history, onlineMVPActualStackHistory] using hgetD
          _ = (onlineRowOutcomes history r).get ⟨0, by rw [hrowCount, hone]; omega⟩ :=
            List.getD_eq_get _ fallback ⟨0, by rw [hrowCount, hone]; omega⟩
          _ = data (r, ⟨0, by omega⟩) := hread
      have hxsSingleton : xs = [data (r, ⟨0, by omega⟩)] := by
        have hval : xs[0]? = some (data (r, ⟨0, by omega⟩)) := by
          have hidx : 0 < xs.length := by rw [hxsLength, hone]; omega
          simp only [List.getElem?_eq_getElem hidx, List.get_eq_getElem]
          exact congrArg some hfirstGet
        apply List.ext_getElem?'
        intro i hi
        have hi0 : i = 0 := by simpa [hxsLength, hone] using hi
        subst i
        simpa [hval]
      have hbatch : onlineMVPSourceBatchList xs = [data (r, ⟨0, by omega⟩)] := by
        rw [hxsSingleton]
        simp [onlineMVPSourceBatchList, onlineMVPSourceBatchStart,
          onlineMVPSourceBatchEnd]
      have hrow := onlineMVPActualStackPlanningRow_eq_sourceBatch
        hH E initial fallback planner data n h s a hpos
      let batch := onlineMVPSourceBatchList xs
      have hbatchLen : batch.length = 1 := by
        change (onlineMVPSourceBatchList xs).length = 1
        rw [hbatch]
        rfl
      have hbatchPos : 0 < batch.length := by rw [hbatchLen]; omega
      have hrowEmp : onlineObservedPlanningRow
          (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
          FiniteDistribution.empiricalRow batch.length hbatchPos (fun q => batch.get q) := by
        simpa [batch, xs, rowAt, nextAt, r] using hrow
      have hbatchDist :
          FiniteDistribution.empiricalRow batch.length hbatchPos (fun q => batch.get q) =
            onlineMVPActualFirstVisitRow data r (by omega) := by
        apply onlineMVP_finiteDistribution_ext (Ω := State)
        intro x
        simp [batch, hbatch, onlineMVPActualFirstVisitRow, FiniteDistribution.empiricalRow]
      have hrow' := hrowEmp.trans hbatchDist
      simpa [mvp_visitRankKernel, u, hzero, hone] using hrow'
    · have hu2 : 2 ≤ u := by omega
      let j := mvp_rankBatchLevel K u huK hu2
      have hloglow : 1 ≤ Nat.log2 u := (Nat.le_log2 (by omega)).2 (by omega)
      have hlog : Nat.log2 u = j.val + 1 := by
        dsimp [j, mvp_rankBatchLevel]
        omega
      have hfloor := onlineMVP_floorPower_le u (by omega : u ≠ 0)
      have hlower : 2^(j.val+1) ≤ u := by simpa [hlog] using hfloor
      have hupper : u < 2^(j.val+2) := by
        simpa [hlog, Nat.add_assoc] using onlineMVP_lt_nextFloorPower u
      have hpow : 2 * 2^j.val = 2^(j.val+1) := by
        rw [Nat.pow_succ]
        ring
      have hbase : 2 * 2^j.val ≤ u := by omega
      let iVal := u - 2 * 2^j.val
      have hdecomp : 2 * 2^j.val + iVal = u := by
        dsimp [iVal]
        omega
      have hi : iVal < 2 * 2^j.val := by
        dsimp [iVal]
        have hupper' : u < 2 * (2 * 2^j.val) := by
          simpa [hlog, Nat.add_assoc, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm] using onlineMVP_lt_nextFloorPower u
        omega
      let i : Fin (2 * 2^j.val) := ⟨iVal, hi⟩
      have hactual : onlineObservedPlanningRow
          (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
          MVPUniformSource.batchRow data j h s a := by
        have huSlot : 2 * 2^j.val + i.val < K := by
          calc
            2 * 2^j.val + i.val = u := hdecomp
            _ = onlineVisitCount rowAt n r := hcount.symm
            _ < K := by simpa [rowAt, r] using huK
        apply onlineMVPActualPlanningRow_eq_sourceBatchRow_at_rank
          hH E initial fallback planner data n hn h s a j i huSlot
        change onlineVisitCount rowAt n r = 2 * 2^j.val + i.val
        rw [hcount]
        exact hdecomp.symm
      have huSlot : 2 * 2^j.val + i.val < K := by
        calc
          2 * 2^j.val + i.val = u := hdecomp
          _ = onlineVisitCount rowAt n r := hcount.symm
          _ < K := by simpa [rowAt, r] using huK
      have hkernel :
          mvp_visitRankKernel K onlineUniformInitialRow
            (onlineMVPActualFirstVisitRow data r (by omega))
            (fun j => MVPUniformSource.batchRow data j h s a) ⟨u, huK⟩ =
          MVPUniformSource.batchRow data j h s a := by
        have hk := mvp_visitRankKernel_at_slot K onlineUniformInitialRow
          (onlineMVPActualFirstVisitRow data r (by omega))
          (fun j => MVPUniformSource.batchRow data j h s a) j i.val hi huSlot
        calc
          mvp_visitRankKernel K onlineUniformInitialRow
              (onlineMVPActualFirstVisitRow data r (by omega))
              (fun j => MVPUniformSource.batchRow data j h s a) ⟨u, huK⟩ =
            mvp_visitRankKernel K onlineUniformInitialRow
              (onlineMVPActualFirstVisitRow data r (by omega))
              (fun j => MVPUniformSource.batchRow data j h s a)
                ⟨2 * 2^j.val + i.val, huSlot⟩ := by
                  apply congrArg (mvp_visitRankKernel K onlineUniformInitialRow
                    (onlineMVPActualFirstVisitRow data r (by omega))
                    (fun j => MVPUniformSource.batchRow data j h s a))
                  apply Fin.ext
                  exact hdecomp.symm
          _ = MVPUniformSource.batchRow data j h s a := hk
      exact hactual.trans hkernel.symm

end StatisticalRL.OnlineRL
