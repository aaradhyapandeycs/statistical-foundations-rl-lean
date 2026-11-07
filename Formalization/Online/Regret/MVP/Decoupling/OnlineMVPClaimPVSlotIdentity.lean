import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualRankRadius
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathW4RankSummand
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler

/-! Per-slot path-to-stack identity for Claim 5.1 (`claim:PV-l-UB`,
`chapters/onlineRL.tex:4340–4353`). For one doubling level `l` and one
within-level index `j`, the episode-indexed sum of signed errors at the
episodes whose pre-episode visit count is `2^(l-1)+j-1` is regrouped into the
row-indexed rank lookup used by the actual stack-slot radius condition. Every
identity here is pathwise under equality of the sequential and finite-stack
transcripts; no probability statement is made in this file. -/

namespace StatisticalRL.OnlineRL

open scoped BigOperators
open StatisticalRL.OnlineRL.MVPProfile
open StatisticalRL.OnlineRL.MVPUniformSource

/-- Regrouping a fixed visit-rank slot: summing over episodes whose pre-count
equals `u` is the same as summing over rows of the (at most one) value with
rank `u`; absent ranks contribute `G r 0 = 0`. -/
theorem mvp_slotSum_eq_rowLookupSum {Row Value : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommMonoid Value] (rows : ℕ → Row) (K u : ℕ) (W : Fin K → Value)
    (G : Row → Value → ℝ) (hG : ∀ r, G r 0 = 0) :
    (∑ k : Fin K, if onlineVisitCount rows k.val (rows k.val) = u
        then G (rows k.val) (W k) else 0) =
      ∑ r : Row, G r (mvp_visitValueLookup rows K r u W) := by
  classical
  have hr : ∀ r : Row, G r (mvp_visitValueLookup rows K r u W) =
      ∑ k : Fin K, if rows k.val = r ∧ onlineVisitCount rows k.val r = u
        then G r (W k) else 0 := by
    intro r
    rw [mvp_visitValueLookup_map rows K r u W (G r) (hG r)]
    unfold mvp_visitValueLookup
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun r _ => hr r), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (rows k.val)]
  · by_cases hc : onlineVisitCount rows k.val (rows k.val) = u
    · rw [if_pos hc, if_pos ⟨rfl, hc⟩]
    · rw [if_neg hc, if_neg (fun h => hc h.2)]
  · intro r _ hne
    rw [if_neg]
    rintro ⟨h1, _⟩
    exact hne h1.symm
  · intro hn
    exact absurd (Finset.mem_univ _) hn

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance claimPVStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance claimPVActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The explicit source batch row `P̂^{(l)}` of Claim 5.1 read from a completed
history: for `l ≥ 2` the empirical row of the successors of `(h,x)` at its
zero-based visits `2^(l-2),…,2^(l-1)-1`; for `l = 1` the first successor. -/
noncomputable def claimPVPathBatch {H : ℕ}
    (history : List (OnlineMDPRow State Action H × State)) (fallback : State)
    (l : ℕ) (h : Fin H) (x : State × Action) : FiniteDistribution State :=
  FiniteDistribution.empiricalRow (2^(l-2)) (by positivity)
    (fun q : Fin (2^(l-2)) => (onlineRowOutcomes history (h, x)).getD
      ((if l = 1 then 0 else 2^(l-2)) + q.val) fallback)

/-- Episode-indexed signed error at one visit-rank slot. -/
noncomputable def claimPVSlotError {H K : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sa : Fin H → ℕ → State × Action) (cnt : Fin H → Fin K → ℕ)
    (Phat : Fin H → Fin K → FiniteDistribution State)
    (U : Fin H → Fin K → State → ℝ) (u : ℕ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    if cnt h k = u then
      (Phat h k).expectation (U h k) -
        ((E h).transition (sa h k.val).1 (sa h k.val).2).expectation (U h k)
    else 0

/-- Episode-indexed true-transition variance at one visit-rank slot. -/
noncomputable def claimPVSlotVariance {H K : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (sa : Fin H → ℕ → State × Action) (cnt : Fin H → Fin K → ℕ)
    (U : Fin H → Fin K → State → ℝ) (u : ℕ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    if cnt h k = u then
      ((E h).transition (sa h k.val).1 (sa h k.val).2).variance (U h k)
    else 0

omit [Fintype State] [Fintype Action] in
/-- Length of a row's outcome list in the actual stack transcript is the
row's visit count. -/
theorem claimPV_stackRowOutcomes_length {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ)
    (r : OnlineMDPRow State Action H) :
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r).length =
      onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data) n r := by
  classical
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let history := onlineMVPActualStackHistory hH initial fallback planner data n
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
  have hcount' := onlineTranscript_rowCount_eq_visitCount history rowAt hrows n
    (by rw [hhistorylen]) r
  have htake : history.take n = history := by
    rw [← hhistorylen]
    exact List.take_length
  rw [htake] at hcount'
  exact hcount'

/-- The stage-tagged actual row at stage `h` of episode `e` is `(h, rows h e)`. -/
theorem claimPV_stackRow_tag {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (h : Fin H) (e : ℕ) :
    onlineMVPActualStackRowAt hH initial fallback planner data (e * H + h.val) =
      (h, mvpActualRankRows hH initial fallback planner data h e) := by
  apply Prod.ext
  · apply Fin.ext
    have hs := onlineMVPActualStackRowAt_stage hH initial fallback planner data
      (e * H + h.val)
    rw [hs, Nat.mul_comm e H, Nat.add_comm (H * e) h.val,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  · rfl

/-- Visit count of a stage-tagged row before episode `k` equals the count of
its state-action pair among the earlier stage-`h` rows. -/
theorem claimPV_stageCount_eq {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (h : Fin H) (k : ℕ)
    (x : State × Action) :
    onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
        (k * H) (h, x) =
      onlineVisitCount (mvpActualRankRows hH initial fallback planner data h) k x := by
  classical
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  have hstage : ∀ j, j < k * H → (rowAt j).1.val = j % H := fun j _ =>
    onlineMVPActualStackRowAt_stage hH initial fallback planner data j
  have hc := onlineVisitCount_stage_episode_eq rowAt h k hH (h, x) rfl hstage
  rw [hc]
  have hfun : (fun e => rowAt (e * H + h.val)) =
      (fun e => (h, mvpActualRankRows hH initial fallback planner data h e)) := by
    funext e
    exact claimPV_stackRow_tag hH initial fallback planner data h e
  rw [hfun]
  unfold onlineVisitCount
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_range, Prod.mk.injEq, true_and]

/-- Path-side selected row equals the stack row, as a function of the episode. -/
theorem claimPV_row_eq {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H))
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback planner data (K * H))
    (h : Fin H) (e : ℕ) (he : e < K) :
    onlineActualStageRowSequence H K hH initial fallback planner path h e =
      mvpActualRankRows hH initial fallback planner data h e :=
  mvpPathSelectedRow_eq_stackRow_of_transcript hH E initial fallback planner data path
    htranscript h ⟨e, he⟩

/-- Path-side pre-episode count equals the stack visit count of the stage row. -/
theorem claimPV_count_eq {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H))
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback planner data (K * H))
    (h : Fin H) (k : Fin K) :
    ((Finset.range k.val).filter (fun e =>
        onlineActualStageRowSequence H K hH initial fallback planner path h e =
          onlineActualStageRowSequence H K hH initial fallback planner path h k.val)).card =
      onlineVisitCount (mvpActualRankRows hH initial fallback planner data h) k.val
        (mvpActualRankRows hH initial fallback planner data h k.val) := by
  classical
  rw [claimPV_row_eq hH E initial fallback planner data path htranscript h k.val k.isLt]
  unfold onlineVisitCount
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨he, hx⟩
    refine ⟨he, ?_⟩
    rw [← claimPV_row_eq hH E initial fallback planner data path htranscript h e
      (lt_trans he k.isLt)]
    exact hx
  · rintro ⟨he, hx⟩
    refine ⟨he, ?_⟩
    rw [claimPV_row_eq hH E initial fallback planner data path htranscript h e
      (lt_trans he k.isLt)]
    exact hx

/-- Path-side continuation value equals the stack rank value. -/
theorem claimPV_value_eq {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H)) (L c₁ c₂ : ℝ)
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback planner data (K * H))
    (h : Fin H) (k : Fin K) :
    onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
      (onlineMVPHistoryPlanningStages hH E fallback
        ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path).take
            (k.val * H))) (h.val + 1) =
      mvpActualRankValues hH E initial fallback planner data L c₁ c₂ h k := by
  have hprefix :
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path).take
          (k.val * H) =
        onlineMVPActualStackHistory hH initial fallback planner data (k.val * H) := by
    rw [htranscript]
    simpa [onlineMVPActualStackHistory] using
      onlineStackHistory_take
        (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) (K * H) (k.val * H)
        (Nat.mul_le_mul_right H k.isLt.le)
  rw [hprefix, onlineMVPHistoryPlanningStages_actualStack_eq]
  rfl

omit [Fintype Action] in
theorem claimPV_empiricalRow_congr {n m : ℕ} (hnm : n = m) (hn : 0 < n) (hm : 0 < m)
    (f : Fin n → State) (g : Fin m → State)
    (hfg : ∀ q : Fin n, f q = g (Fin.cast hnm q)) :
    FiniteDistribution.empiricalRow n hn f = FiniteDistribution.empiricalRow m hm g := by
  subst hnm
  congr 1
  funext q
  exact hfg q

/-- At a visit with pre-count at least `2·2^jL`, the explicit path batch row of
level `jL+2` is the stack batch row of finite level `jL`. -/
theorem claimPV_batch_eq {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H))
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback planner data (K * H))
    (h : Fin H) (k : Fin K) (jL : ℕ) (hjL : jL < Nat.log2 K)
    (hcount : 2 * 2^jL ≤ onlineVisitCount (mvpActualRankRows hH initial fallback planner data h)
      k.val (mvpActualRankRows hH initial fallback planner data h k.val)) :
    claimPVPathBatch
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path)
      fallback (jL + 2) h (mvpActualRankRows hH initial fallback planner data h k.val) =
      mvpActualRankBatch data h (mvpActualRankRows hH initial fallback planner data h k.val)
        ⟨jL, hjL⟩ := by
  classical
  let x := mvpActualRankRows hH initial fallback planner data h k.val
  let r : OnlineMDPRow State Action H := (h, x)
  have hlen : 2 * 2^jL ≤
      (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data (K * H))
        r).length := by
    rw [claimPV_stackRowOutcomes_length]
    calc
      2 * 2^jL ≤ onlineVisitCount (mvpActualRankRows hH initial fallback planner data h)
          k.val x := hcount
      _ = onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
          (k.val * H) r := (claimPV_stageCount_eq hH initial fallback planner data h k.val x).symm
      _ ≤ onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
          (K * H) r := onlineVisitCount_mono _ (Nat.mul_le_mul_right H k.isLt.le) r
  unfold claimPVPathBatch mvpActualRankBatch MVPUniformSource.batchRow
  rw [htranscript]
  apply claimPV_empiricalRow_congr (by simp)
  intro q
  have hq : q.val < 2^jL := by simpa using q.isLt
  have hidx : 2^jL + q.val <
      (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data (K * H))
        r).length := by omega
  have hif : (if jL + 2 = 1 then 0 else 2^(jL + 2 - 2)) = 2^jL := by
    rw [if_neg (by omega)]
    simp
  change (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data (K * H))
      r).getD ((if jL + 2 = 1 then 0 else 2^(jL + 2 - 2)) + q.val) fallback = _
  rw [hif, List.getD_eq_get _ fallback ⟨2^jL + q.val, hidx⟩,
    onlineMVPActualStackHistory_rowNth_eq_stack hH initial fallback planner data (K * H) le_rfl r
      ⟨2^jL + q.val, hidx⟩]
  rfl

/-- Per-slot bound at source level `l = jL+2` and within-level index `i+1`,
on the actual value-family event and transcript equality. -/
theorem claimPV_slot_bound {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H))
    (hL : L = Real.log (1 / onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K))
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualValueSourceFamily hH E L c₁ c₂))
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂)) (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂) data (K * H))
    (jL : ℕ) (hjL : jL < Nat.log2 K) (i : ℕ) (hi : i < 2 * 2^jL) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let sa := fun (h : Fin H) (e : ℕ) =>
      onlineActualStageRowSequence H K hH initial fallback planner path h e
    let cnt := fun (h : Fin H) (k : Fin K) =>
      ((Finset.range k.val).filter (fun e => sa h e = sa h k.val)).card
    let U := fun (h : Fin H) (k : Fin K) =>
      onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
        (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))) (h.val + 1)
    let Phat := fun (h : Fin H) (k : Fin K) =>
      claimPVPathBatch history fallback (jL + 2) h (sa h k.val)
    let d := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card (Fin H × (State × Action)))) * L
    claimPVSlotError E sa cnt Phat U (2 * 2^jL + i) ≤
      Real.sqrt (d * I * ((1:ℝ) / (16 * (2:ℝ)^jL * (Real.log K / Real.log 2))) *
        claimPVSlotVariance E sa cnt U (2 * 2^jL + i)) +
      (d * H * I) * ((1:ℝ) / (16 * (2:ℝ)^jL * (Real.log K / Real.log 2))) := by
  classical
  intro planner history sa cnt U Phat d I
  let rows := mvpActualRankRows hH initial fallback planner data
  let V := mvpActualRankValues hH E initial fallback planner data L c₁ c₂
  let p := mvpActualRankTransition E
  let q0 := mvpActualRankInitial E hH
  let q1 := mvpActualRankFirst (by omega : 0 < K) data
  let qb := mvpActualRankBatch data
  let jf : Fin (Nat.log2 K) := ⟨jL, hjL⟩
  let u := 2 * 2^jL + i
  have hcond : mvp_rankSlotRadiusCondition rows K V p q0 q1 qb d (H : ℝ) I :=
    mvp_actualRankSlotRadiusCondition_of_valueEvent hH hK E δ L c₁ c₂ initial fallback
      planner data hL hgood
  have hslot := hcond jL hjL i hi
  have hrow (h : Fin H) (k : Fin K) : sa h k.val = rows h k.val :=
    claimPV_row_eq hH E initial fallback planner data path htranscript h k.val k.isLt
  have hcnt (h : Fin H) (k : Fin K) :
      cnt h k = onlineVisitCount (rows h) k.val (rows h k.val) :=
    claimPV_count_eq hH E initial fallback planner data path htranscript h k
  have hval (h : Fin H) (k : Fin K) : U h k = V h k :=
    claimPV_value_eq hH E initial fallback planner data path L c₁ c₂ htranscript h k
  have herr : claimPVSlotError E sa cnt Phat U u =
      ∑ h : Fin H, ∑ r : State × Action,
        ((qb h r jf).expectation (mvp_visitValueLookup (rows h) K r u (V h)) -
          (p h r).expectation (mvp_visitValueLookup (rows h) K r u (V h))) := by
    unfold claimPVSlotError
    apply Finset.sum_congr rfl
    intro h _
    rw [← mvp_slotSum_eq_rowLookupSum (rows h) K u (V h)
      (fun r W => (qb h r jf).expectation W - (p h r).expectation W)
      (fun r => by
        change (qb h r jf).expectation (fun _ => 0) - (p h r).expectation (fun _ => 0) = 0
        simp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcnt h k]
    by_cases hc : onlineVisitCount (rows h) k.val (rows h k.val) = u
    · rw [if_pos hc, if_pos hc]
      have hbatch : Phat h k = qb h (rows h k.val) jf := by
        change claimPVPathBatch history fallback (jL + 2) h (sa h k.val) = _
        rw [hrow h k]
        exact claimPV_batch_eq hH initial fallback planner data path htranscript h k jL hjL
          (by rw [hc]; omega)
      rw [hbatch, hval h k, hrow h k]
      rfl
    · rw [if_neg hc, if_neg hc]
  have hvar : claimPVSlotVariance E sa cnt U u =
      ∑ h : Fin H, ∑ r : State × Action,
        (p h r).variance (mvp_visitValueLookup (rows h) K r u (V h)) := by
    unfold claimPVSlotVariance
    apply Finset.sum_congr rfl
    intro h _
    rw [← mvp_slotSum_eq_rowLookupSum (rows h) K u (V h)
      (fun r W => (p h r).variance W)
      (fun r => by
        change (p h r).variance (fun _ => 0) = 0
        simp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcnt h k]
    by_cases hc : onlineVisitCount (rows h) k.val (rows h k.val) = u
    · rw [if_pos hc, if_pos hc, hval h k, hrow h k]
      rfl
    · rw [if_neg hc, if_neg hc]
  have hpos : (∑ h : Fin H, ∑ r : State × Action,
        ((qb h r jf).expectation (mvp_visitValueLookup (rows h) K r u (V h)) -
          (p h r).expectation (mvp_visitValueLookup (rows h) K r u (V h)))) ≤
      ∑ h : Fin H, ∑ r : State × Action,
        mvp_rankErrorAt (rows h) K r (V h) (p h r) (q0 h r) (q1 h r) (qb h r) u := by
    apply Finset.sum_le_sum
    intro h _
    apply Finset.sum_le_sum
    intro r _
    unfold mvp_rankErrorAt
    rw [mvp_rankPositiveError_lookup_at_slot (rows h) K r (V h) (p h r) (q0 h r) (q1 h r)
      (qb h r) jf i hi]
    unfold mvp_rowPositiveError
    exact le_max_left _ _
  rw [herr, hvar]
  exact le_trans hpos hslot

end StatisticalRL.OnlineRL
