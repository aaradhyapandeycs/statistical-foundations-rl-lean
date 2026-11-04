import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPCommittedModel
import Formalization.Online.SourceOptimism.StackSequentialLawEquality
import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Formalization.Online.Regret.MVP.MVPActualProfiles
import Mathlib.Data.List.GetD

/-! An actual finite-stack causal sampler for the episodic MDP transcript.
The full reset/transcript law identity is imported; this file adds the
MVP-oriented rowAt/nextAt bridge and finite per-row stream index bound. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpSamplerStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance mvpSamplerStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpSamplerActionDecidable : DecidableEq Action := Classical.decEq Action
local instance mvpSamplerTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance mvpSamplerSequentialMeasurable (H K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

/-- The actual finite product of independent successor stacks and episode
reset coordinates used by the source protocol. -/
noncomputable abbrev onlineMVPActualStackLaw {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State) (K : ℕ) :=
  onlineMDPInitialStackLaw E ρ K

/-- Run the actual stage-clock/reset/action selector against a finite stack
array, reading the next unused coordinate of each selected row. -/
noncomputable def onlineMVPActualStackHistory {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :
    List (OnlineMDPRow State Action H × State) :=
  onlineStackHistory (onlineEpisodicChoose H K hH initial fallback planner)
    (onlineFiniteStackExtend K fallback data) n

/-- The row chosen at clock n from the actual revealed stack transcript. -/
noncomputable def onlineMVPActualStackRowAt {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :
    OnlineMDPRow State Action H :=
  onlineEpisodicChoose H K hH initial fallback planner
    (onlineMVPActualStackHistory hH initial fallback planner data n)

/-- The exact unused stack coordinate read at clock n. -/
noncomputable def onlineMVPActualStackNextAt {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) : State :=
  onlineFiniteStackExtend K fallback data
    (onlineMVPActualStackRowAt hH initial fallback planner data n)
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n)
      (onlineMVPActualStackRowAt hH initial fallback planner data n)).length

/-- One actual chronological record is precisely the source row selected from
the pre-record history and that row's next unused stack coordinate. -/
theorem onlineMVPActualStackHistory_succ
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :
    onlineMVPActualStackHistory hH initial fallback planner data (n + 1) =
      onlineMVPActualStackHistory hH initial fallback planner data n ++
        [(onlineMVPActualStackRowAt hH initial fallback planner data n,
          onlineMVPActualStackNextAt hH initial fallback planner data n)] := by
  rfl

/-- For every row, filtering the actual `rowAt`/`nextAt` arrays through time n
is exactly the row's observed successor list in the sampler transcript. -/
theorem onlineMVPActualStackHistory_rowVisitList
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ)
    (r : OnlineMDPRow State Action H) :
    onlineMVPRowVisitList
      (onlineMVPActualStackRowAt hH initial fallback planner data)
      (onlineMVPActualStackNextAt hH initial fallback planner data) n r =
    onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r := by
  induction n with
  | zero =>
      change onlineMVPRowVisitList
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) 0 r =
        onlineRowOutcomes [] r
      rfl
  | succ n ih =>
      rw [onlineMVPRowVisitList_succ, onlineMVPActualStackHistory_succ,
        onlineRowOutcomes_append_one, ih]

/-- Every selected row has the actual stage `n % H`; this is the source clock,
not a free row-sequence assumption. -/
theorem onlineMVPActualStackRowAt_stage
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :
    (onlineMVPActualStackRowAt hH initial fallback planner data n).1.val = n % H := by
  change (onlineEpisodicChoose H K hH initial fallback planner
      (onlineStackHistory (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) n)).1.val = n % H
  rw [onlineEpisodicChoose_stage]
  rw [onlineStackHistory_length]

/-- At every time before the source horizon, the selected row's draw index is
strictly below the K-coordinate finite stack. The row tag equals the current
stage, so its earlier occurrences inject into strictly earlier episodes. -/
theorem onlineMVPActualStackNext_index_lt
    {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n < K * H) :
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n)
      (onlineMVPActualStackRowAt hH initial fallback planner data n)).length < K := by
  classical
  let history := onlineMVPActualStackHistory hH initial fallback planner data n
  let row := onlineMVPActualStackRowAt hH initial fallback planner data n
  let rows : ℕ → OnlineMDPRow State Action H :=
    fun j => onlineMVPActualStackRowAt hH initial fallback planner data j
  have hlen : history.length = n := by
    simpa [history, onlineMVPActualStackHistory] using
      onlineStackHistory_length _ _ n
  have hrows : ∀ j : Fin history.length, rows j.val = (history.get j).1 := by
    intro j
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let stream := onlineFiniteStackExtend K fallback data
    have hhist : onlineStackHistory choose stream history.length = history := by
      rw [hlen]
      rfl
    have hsteps := (onlineStackHistory_eq_iff_transcriptSteps choose stream history).mp hhist
    have hconsistent := (onlineTranscriptSteps_iff_rows_and_coordinates choose stream history).mp hsteps |>.1
    have htake : history.take j.val = onlineStackHistory choose stream j.val := by
      simpa [hlen, choose, stream] using
        (onlineStackHistory_take choose stream history.length j.val j.isLt.le)
    have hrow := hconsistent j
    calc
      rows j.val = choose (onlineStackHistory choose stream j.val) := by
        simp [rows, onlineMVPActualStackRowAt, onlineMVPActualStackHistory, choose, stream]
      _ = choose (history.take j.val) := congrArg choose htake.symm
      _ = (history.get j).1 := hrow.symm
  have hle : n ≤ history.length := by omega
  have hvisit := onlineTranscript_rowCount_eq_visitCount history rows hrows n hle row
  have htakeN : history.take n = history := by simpa [hlen] using List.take_length history
  have hvisit' : (onlineRowOutcomes history row).length = onlineVisitCount rows n row := by
    rw [← htakeN]
    exact hvisit
  change (onlineRowOutcomes history row).length < K
  rw [hvisit']
  let h : Fin H := ⟨n % H, Nat.mod_lt _ hH⟩
  have hrowtag : row.1 = h := by
    apply Fin.ext
    exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
  have hstage (j : ℕ) (hj : j < n) : (rows j).1.val = j % H := by
    exact onlineMVPActualStackRowAt_stage hH initial fallback planner data j
  have hstageAll (j : ℕ) (hj : j < (n / H) * H) :
      (rows j).1.val = j % H := hstage j (by
        have hq : (n / H) * H ≤ n := Nat.div_mul_le_self n H
        omega)
  have hn_decomp : n = n / H * H + n % H := by
    calc
      n = n % H + H * (n / H) := (Nat.mod_add_div n H).symm
      _ = n / H * H + n % H := by ring
  have hstageCount : onlineVisitCount rows n row =
      onlineVisitCount rows ((n / H) * H) row := by
    unfold onlineVisitCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hjn, hrow⟩
      by_cases hbefore : j < (n / H) * H
      · exact ⟨hbefore, hrow⟩
      · have hge : (n / H) * H ≤ j := by omega
        let i := j - (n / H) * H
        have hdecomp : j = (n / H) * H + i := by dsimp [i]; omega
        have hi : i < n % H := by
          rw [hn_decomp] at hjn
          dsimp [i]
          omega
        have hiH : i < H := lt_trans hi (Nat.mod_lt _ hH)
        have hmod : j % H = i := by
          rw [hdecomp, Nat.mul_comm (n / H) H,
            Nat.add_comm (H * (n / H)) i,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hiH]
        have hrowtag := congrArg (fun x : OnlineMDPRow State Action H => x.1.val) hrow
        have hstagej := hstage j hjn
        have hi_eq : i = n % H := by
          calc
            i = j % H := hmod.symm
            _ = (rows j).1.val := hstagej.symm
            _ = row.1.val := by simpa [row] using hrowtag
            _ = n % H := onlineMVPActualStackRowAt_stage hH initial fallback planner data n
        omega
    · rintro ⟨hjq, hrow⟩
      exact ⟨by omega, hrow⟩
  rw [hstageCount]
  have hrowStage : row.1 = h := hrowtag
  rw [onlineVisitCount_stage_episode_eq rows h (n / H) hH row hrowStage hstageAll]
  have hcount : onlineVisitCount (fun e => rows (e * H + h.val)) (n / H) row ≤ n / H :=
    StatisticalRL.OnlineRL.MVPProfile.onlineVisitCount_le_prefix _ _ _
  have hK : n / H < K := (Nat.div_lt_iff_lt_mul hH).2 (by simpa [Nat.mul_comm] using hn)
  exact lt_of_le_of_lt hcount hK

/-- A fixed stage/state/action row can occur at most once per episode, hence
at most K times in any actual K-episode stack transcript prefix. -/
theorem onlineMVPActualStackHistory_rowCount_le_K
    {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K * H) (r : OnlineMDPRow State Action H) :
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r).length ≤ K := by
  classical
  let history := onlineMVPActualStackHistory hH initial fallback planner data n
  let rows : ℕ → OnlineMDPRow State Action H :=
    fun j => onlineMVPActualStackRowAt hH initial fallback planner data j
  have hlen : history.length = n := by
    simpa [history, onlineMVPActualStackHistory] using onlineStackHistory_length _ _ n
  have hrows : ∀ j : Fin history.length, rows j.val = (history.get j).1 := by
    intro j
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let stream := onlineFiniteStackExtend K fallback data
    have hhist : onlineStackHistory choose stream history.length = history := by
      rw [hlen]
      rfl
    have hsteps := (onlineStackHistory_eq_iff_transcriptSteps choose stream history).mp hhist
    have hconsistent := (onlineTranscriptSteps_iff_rows_and_coordinates choose stream history).mp hsteps |>.1
    have htake : history.take j.val = onlineStackHistory choose stream j.val := by
      simpa [hlen, choose, stream] using
        (onlineStackHistory_take choose stream history.length j.val j.isLt.le)
    have hrow := hconsistent j
    calc
      rows j.val = choose (onlineStackHistory choose stream j.val) := by
        simp [rows, onlineMVPActualStackRowAt, onlineMVPActualStackHistory, choose, stream]
      _ = choose (history.take j.val) := congrArg choose htake.symm
      _ = (history.get j).1 := hrow.symm
  have hle : n ≤ history.length := by omega
  have hvisit := onlineTranscript_rowCount_eq_visitCount history rows hrows n hle r
  have htakeN : history.take n = history := by simpa [hlen] using List.take_length history
  have hvisit' : (onlineRowOutcomes history r).length = onlineVisitCount rows n r := by
    rw [← htakeN]
    exact hvisit
  change (onlineRowOutcomes history r).length ≤ K
  rw [hvisit']
  have hfull : onlineVisitCount rows n r ≤ onlineVisitCount rows (K * H) r :=
    StatisticalRL.OnlineRL.MVPProfile.onlineVisitCount_mono rows hn r
  have hstage (j : ℕ) (hj : j < K * H) : (rows j).1.val = j % H := by
    exact onlineMVPActualStackRowAt_stage hH initial fallback planner data j
  have hstageCount := onlineVisitCount_stage_episode_eq rows r.1 K hH r rfl hstage
  calc
    onlineVisitCount rows n r ≤ onlineVisitCount rows (K * H) r := hfull
    _ = onlineVisitCount (fun e => rows (e * H + r.1.val)) K r := hstageCount
    _ ≤ K := StatisticalRL.OnlineRL.MVPProfile.onlineVisitCount_le_prefix _ _ _

/-- The ith observation at a fixed row in the actual sampler is the ith
unused product-stack draw for that row. Positivity of the random row count is
not needed; the finite coordinate exists by the pathwise stage-clock bound. -/
theorem onlineMVPActualStackHistory_rowNth_eq_stack
    {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K * H) (r : OnlineMDPRow State Action H)
    (i : Fin (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r).length) :
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r).get i =
      data (r, ⟨i.val, by
        have hcount := onlineMVPActualStackHistory_rowCount_le_K hH initial fallback planner data n hn r
        omega⟩) := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  have hprefix := onlineStackHistory_row_prefix choose stream n r
  have hread : i.val < K := by
    have hcount := onlineMVPActualStackHistory_rowCount_le_K hH initial fallback planner data n hn r
    omega
  have hget : (onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data n) r).get i =
      data (r, ⟨i.val, hread⟩) := by
    change (onlineRowOutcomes (onlineStackHistory choose stream n) r).get i = _
    have hgetD := congrArg (fun xs : List State => xs.getD i.val fallback) hprefix
    calc
      (onlineRowOutcomes (onlineStackHistory choose stream n) r).get i =
          (onlineRowOutcomes (onlineStackHistory choose stream n) r).getD i.val fallback :=
        (List.getD_eq_get _ fallback i).symm
      _ = (List.map (stream r)
          (List.range (onlineRowOutcomes (onlineStackHistory choose stream n) r).length)).getD
            i.val fallback := hgetD
      _ = data (r, ⟨i.val, hread⟩) := by
        have hmaplen : (List.map (stream r)
            (List.range (onlineRowOutcomes (onlineStackHistory choose stream n) r).length)).length =
            (onlineRowOutcomes (onlineStackHistory choose stream n) r).length := by simp
        have hidx : i.val <
            (List.map (stream r)
              (List.range (onlineRowOutcomes (onlineStackHistory choose stream n) r).length)).length := by
          simpa [hmaplen, onlineMVPActualStackHistory, choose, stream] using i.isLt
        have hgetMap := List.getD_eq_get _ fallback ⟨i.val, hidx⟩
        rw [hgetMap]
        simp [stream, onlineFiniteStackExtend, hread]
  simpa [onlineFiniteStackExtend] using hget

/- The generic, exact reset/transcript law equality is exported as
`onlineStack_sequential_transcriptLaw_eq`; instantiate its planner argument
directly at `onlineMVPCommittedGreedyPlanner` when consuming this sampler. -/

theorem onlineMVPHistoryRowAt_eq_record {H : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State))
    (n : ℕ) (hn : n < history.length) :
    onlineMVPHistoryRowAt hH E fallback history n = (history.get ⟨n, hn⟩).1 := by
  simp [onlineMVPHistoryRowAt, hn]

theorem onlineMVPHistoryNextAt_eq_record {H : ℕ} (fallback : State)
    (history : List (OnlineMDPRow State Action H × State))
    (n : ℕ) (hn : n < history.length) :
    onlineMVPHistoryNextAt fallback history n = (history.get ⟨n, hn⟩).2 := by
  simp [onlineMVPHistoryNextAt, hn]

/-- The source planner's chosen action maximizes the retained-batch capped Q
table computed from its completed actual transcript. -/
theorem onlineMVPCommittedGreedyPlanner_max {H : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H) (s : State) :
    letI : Nonempty Action := (E h).action_nonempty
    onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
      (onlineMVPHistoryPlanningStages hH E fallback history) h.val s
      (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂ history h s) =
    actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
      (onlineMVPHistoryPlanningStages hH E fallback history) h.val s) := by
  letI : Nonempty Action := (E h).action_nonempty
  exact Classical.choose_spec (EnvironmentStage.exists_maximizer _)

/-- Instantiate the causal stack sampler with the retained-batch MVP planner. -/
noncomputable def onlineMVPSourceStackHistory {H K : ℕ}
    (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (L c₁ c₂ : ℝ)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :=
  onlineMVPActualStackHistory hH initial fallback
    (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂) data n

/-- On an observed transcript record, the arrays consumed by the committed
model are exactly the row and successor fields of that record. -/
theorem onlineMVPHistoryArrays_record
    {H : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (history : List (OnlineMDPRow State Action H × State))
    (n : ℕ) (hn : n < history.length) :
    (onlineMVPHistoryRowAt hH E fallback history n,
      onlineMVPHistoryNextAt fallback history n) = history.get ⟨n, hn⟩ := by
  exact Prod.ext (onlineMVPHistoryRowAt_eq_record hH E fallback history n hn)
    (onlineMVPHistoryNextAt_eq_record fallback history n hn)

/-- The source stage clock is built into the actual sampler. -/
theorem onlineMVPSourceStackHistory_episode_clock
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (L c₁ c₂ : ℝ)
    (data : OnlineMDPRow State Action H × Fin K → State) (n : ℕ) :
    (onlineMVPActualStackRowAt hH initial fallback
      (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂) data n).1.val = n % H :=
  onlineMVPActualStackRowAt_stage hH initial fallback
    (onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂) data n

/-- At a positive stored count, the actual MVP planning row at a sampler
prefix is the empirical distribution of the source dyadic batch extracted
from that very sampler transcript. -/
theorem onlineMVPActualStackPlanningRow_eq_sourceBatch
    {H K : ℕ} [Nonempty State] (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (h : Fin H) (s : State) (a : Action)
    (hpos : 0 < (onlineMVPCommittedTablesRun
      (onlineMVPActualStackRowAt hH initial fallback planner data)
      (onlineMVPActualStackNextAt hH initial fallback planner data) n).base.stored
        (h, (s, a))) :
    onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n h) s a =
    FiniteDistribution.empiricalRow
      (onlineMVPSourceBatchList (onlineMVPRowVisitList
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n (h, (s, a)))).length
      (by
        let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
        let nextAt := onlineMVPActualStackNextAt hH initial fallback planner data
        have hlen := onlineMVPActualBatch_length_eq_committedStored rowAt nextAt n (h, (s, a))
        rw [hlen]
        exact hpos)
      (fun i => (onlineMVPSourceBatchList (onlineMVPRowVisitList
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n (h, (s, a)))).get i) := by
  classical
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let nextAt := onlineMVPActualStackNextAt hH initial fallback planner data
  have hstage := onlineMVPActualPlanningStage_row_eq_committed E rowAt nextAt n h s a
  rw [hstage]
  have hbatch := onlineMVPCommittedPlanningRow_eq_actualBatch rowAt nextAt n (h, (s, a)) hpos
  exact hbatch

/-- At zero stored count, the actual stack-derived MVP row is exactly the
source uniform initialization; this branch does not use an empirical row. -/
theorem onlineMVPActualStackPlanningRow_eq_uniform_of_zero
    {H K : ℕ} [Nonempty State] (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (h : Fin H) (s : State) (a : Action)
    (hzero : (onlineMVPCommittedTablesRun
      (onlineMVPActualStackRowAt hH initial fallback planner data)
      (onlineMVPActualStackNextAt hH initial fallback planner data) n).base.stored
        (h, (s, a)) = 0) :
    onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n h) s a =
      onlineMVPUniformDistribution := by
  classical
  exact onlineMVPActualPlanningStage_row_eq_committed E
    (onlineMVPActualStackRowAt hH initial fallback planner data)
    (onlineMVPActualStackNextAt hH initial fallback planner data) n h s a |>.trans
      (onlineMVPCommittedPlanningRow_eq_uniform_of_zero
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) n (h, (s, a)) hzero)

/- The same imported equality specializes to the source planner by
`onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback
(onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂) n hn`. -/

end StatisticalRL.OnlineRL
