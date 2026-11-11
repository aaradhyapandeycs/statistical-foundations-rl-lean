import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPRowDyadicBatch
import Formalization.Online.SourceOptimism.CappedBackwardRecursion
import Formalization.Online.SourceOptimism.ObservedHistoryPlanningAdapter
import Formalization.Probability.EmpiricalRow
import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A source-shaped finite model for the actual committed MVP row batch.
The row is constructed from the retained integer histogram and its proved
stored mass.  Positive mass is normalized as an empirical row; zero mass uses
the source's separate uniform initialization.  No correctness field or
positivity hypothesis is stored in the model. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open StatisticalRL.OnlineRL.MVPProfile

variable {Outcome : Type*} [Fintype Outcome]
noncomputable local instance outcomeDecidableEq : DecidableEq Outcome := Classical.decEq Outcome

/-- Extensionality for the project's finite probability-vector structure. -/
theorem onlineMVP_finiteDistribution_ext {Ω : Type*} [Fintype Ω]
    (p q : FiniteDistribution Ω) (h : ∀ x, p.prob x = q.prob x) : p = q :=
  FiniteDistribution.ext (funext h)

/-- A finite-list indicator sum is the count of the selected value. -/
theorem onlineMVP_list_count_eq_fin_indicator_sum (xs : List Outcome) (x : Outcome) :
    (xs.count x : ℕ) =
      ∑ i : Fin xs.length, if xs.get i = x then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp [List.count_cons, ih, Nat.add_comm]

/-- The probability vector defined by an integer histogram of total mass `N`.
The normalization proof consumes the actual mass identity. -/
noncomputable def onlineMVPHistogramDistribution (N : ℕ) (hist : Outcome → ℕ)
    (hN : 0 < N) (hmass : (∑ x : Outcome, hist x) = N) :
    FiniteDistribution Outcome where
  prob x := (N : ℝ)⁻¹ * (hist x : ℝ)
  prob_nonneg x := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Nat.cast_nonneg _)
  sum_prob := by
    rw [← Finset.mul_sum]
    have hcast : (∑ x : Outcome, (hist x : ℝ)) = (N : ℝ) := by
      exact_mod_cast hmass
    rw [hcast]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hN))

/-- The list empirical row has exactly the normalized histogram probabilities.
This connects the project's `Fin N` sample API to chronological batch counts. -/
theorem onlineMVP_empiricalRow_prob_eq_count (xs : List Outcome) (x : Outcome)
    (hxs : 0 < xs.length) :
    (FiniteDistribution.empiricalRow xs.length hxs (fun i => xs.get i)).prob x =
      (xs.length : ℝ)⁻¹ * (xs.count x : ℝ) := by
  simp only [FiniteDistribution.empiricalRow]
  have hsum : (∑ i : Fin xs.length,
      if xs.get i = x then (1 : ℝ) else 0) = (xs.count x : ℝ) := by
    exact_mod_cast (onlineMVP_list_count_eq_fin_indicator_sum xs x).symm
  exact congrArg (fun z : ℝ => (xs.length : ℝ)⁻¹ * z) hsum

/-- A table's committed histogram, normalized using its own stored count.
The required mass identity is explicit and is discharged for actual runs below. -/
noncomputable def onlineMVPCommittedHistogramDistribution
    (hist : Outcome → ℕ) (N : ℕ) (hN : 0 < N)
    (hmass : (∑ x : Outcome, hist x) = N) : FiniteDistribution Outcome :=
  onlineMVPHistogramDistribution N hist hN hmass

/-- Uniform row used only before a row has any committed batch. -/
noncomputable def onlineMVPUniformDistribution [Nonempty Outcome] :
    FiniteDistribution Outcome where
  prob _ := (Fintype.card Outcome : ℝ)⁻¹
  prob_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_prob := by
    have hcard : (Fintype.card Outcome : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

/-- The actual MVP row represented by a retained committed histogram.  It is
uniform at zero stored count and normalized from the committed successor
counts at positive stored count. -/
noncomputable def onlineMVPCommittedPlanningRow [Nonempty Outcome]
    {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) :
    FiniteDistribution Outcome := by
  let st := onlineMVPCommittedTablesRun rowAt nextAt n
  by_cases hN : 0 < st.base.stored r
  · exact onlineMVPCommittedHistogramDistribution (st.committed r)
      (st.base.stored r) hN (onlineMVPCommittedTablesRun_mass_eq_stored rowAt nextAt n r)
  · exact onlineMVPUniformDistribution

/-- The MVP source profile index is zero exactly at the unvisited initial row,
one at the first sample, and thereafter stores the preceding half-power batch. -/
theorem onlineMVP_storedCount_eq_profile_batch (n : ℕ) :
    onlineMVPStoredCount n =
      if sourceMVPProfileIndex n = 0 then 0
      else if sourceMVPProfileIndex n = 1 then 1
      else 2 ^ (sourceMVPProfileIndex n - 2) := by
  by_cases h0 : n = 0
  · subst n
    simp [sourceMVPProfileIndex, onlineMVPStoredCount, onlineMVPRowCountState]
  · by_cases h1 : n = 1
    · subst n
      decide
    · have hn : 2 ≤ n := by omega
      have hlog : 1 ≤ Nat.log2 n := by
        apply (Nat.le_log2 (by omega : n ≠ 0)).2
        exact hn
      have hprofile : sourceMVPProfileIndex n = Nat.log2 n + 1 := by
        simp [sourceMVPProfileIndex, h0]
      rw [onlineMVP_storedCount_closedForm, if_neg (by omega)]
      rw [hprofile]
      simp only [if_neg (by omega : Nat.log2 n + 1 ≠ 0),
        if_neg (by omega : Nat.log2 n + 1 ≠ 1)]
      have hexp : Nat.log2 n + 1 - 2 = Nat.log2 n - 1 := by omega
      rw [hexp]

/-- At profile level `j ≥ 2`, the retained batch is exactly the source's
half-power interval `[2^(j-2), 2^(j-1))` in zero-based visit indices. -/
theorem onlineMVPSourceBatch_bounds_profile (n : ℕ) (hn : 2 ≤ n) :
    let j := sourceMVPProfileIndex n
    onlineMVPSourceBatchStart n = 2 ^ (j - 2) ∧
      onlineMVPSourceBatchEnd n = 2 ^ (j - 1) := by
  have h0 : n ≠ 0 := by omega
  have hlog : 1 ≤ Nat.log2 n := by
    apply (Nat.le_log2 h0).2
    simpa using hn
  have hj : sourceMVPProfileIndex n = Nat.log2 n + 1 := by
    simp [sourceMVPProfileIndex, h0]
  dsimp
  constructor
  · rw [onlineMVPSourceBatchStart, if_neg (by omega : ¬ n < 2),
      onlineMVP_storedCount_closedForm, if_neg (by omega : ¬ n < 2), hj]
    congr 1 <;> omega
  · rw [onlineMVPSourceBatchEnd, if_neg (by omega : ¬ n < 2),
      onlineMVP_storedCount_closedForm, if_neg (by omega : ¬ n < 2), hj]
    have hright : Nat.log2 n + 1 - 1 = Nat.log2 n := by omega
    rw [hright]
    calc
      2 * 2 ^ (Nat.log2 n - 1) = 2 ^ (Nat.log2 n - 1) * 2 := by ring
      _ = 2 ^ (Nat.log2 n - 1 + 1) := by rw [Nat.pow_succ]
      _ = 2 ^ Nat.log2 n := by congr 1 <;> omega

/-- The actual committed model's zero/first/positive-batch branch is selected
by the same source profile of the actual row visit count. -/
theorem onlineMVPCommittedPlanningRow_profile_index
    {Row : Type*} [Nonempty Outcome] [DecidableEq Row]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) :
    (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r =
      if sourceMVPProfileIndex (onlineVisitCount rowAt n r) = 0 then 0
      else if sourceMVPProfileIndex (onlineVisitCount rowAt n r) = 1 then 1
      else 2 ^ (sourceMVPProfileIndex (onlineVisitCount rowAt n r) - 2) := by
  have herase := onlineMVPCommittedTablesErase_run rowAt nextAt n
  have hbase : (onlineMVPCommittedTablesRun rowAt nextAt n).base =
      onlineMVPCountTablesRun rowAt nextAt n := by
    simpa [onlineMVPCommittedTablesErase] using herase
  have hstored := (onlineMVPCountTablesRun_row_invariant rowAt nextAt n r).2.2
  rw [← hbase] at hstored
  rw [hstored, onlineMVP_storedCount_eq_profile_batch]

/-- The source dyadic batch length equals the actual stored count of the
operational tables, without an assumed count-correctness field. -/
theorem onlineMVPActualBatch_length_eq_committedStored
    {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) :
    (onlineMVPSourceBatchList (onlineMVPRowVisitList rowAt nextAt n r)).length =
      (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r := by
  let st := onlineMVPCommittedTablesRun rowAt nextAt n
  let xs := onlineMVPRowVisitList rowAt nextAt n r
  let batch := onlineMVPSourceBatchList xs
  rw [onlineMVPSourceBatchList_length]
  have hrow := onlineMVPCommittedTablesRun_row_eq_visitList rowAt nextAt n r
  have htotal := congrArg (fun z : OnlineMVPRowBatchState Outcome => z.total) hrow
  have hscalar := onlineMVPRowBatchStateRun_scalar (xs := xs)
  have hvisit : xs.length = (onlineMVPCommittedTablesRun rowAt nextAt n).base.total r := by
    simpa [xs, onlineMVPCommittedRowView] using hscalar.1.symm.trans htotal
  have herase := onlineMVPCommittedTablesErase_run rowAt nextAt n
  have hbase : (onlineMVPCommittedTablesRun rowAt nextAt n).base =
      onlineMVPCountTablesRun rowAt nextAt n := by
    simpa [onlineMVPCommittedTablesErase] using herase
  have hstored := (onlineMVPCountTablesRun_row_invariant rowAt nextAt n r).2.2
  rw [← hbase] at hstored
  have htotalCount := (onlineMVPCountTablesRun_row_invariant rowAt nextAt n r).1
  rw [← hbase] at htotalCount
  have hcount : xs.length = onlineVisitCount rowAt n r := by
    rw [hvisit, htotalCount]
  rw [hcount]
  simpa [st] using hstored.symm

/-- For every positive-count row, the retained table model equals the actual
empirical row of its chronological dyadic batch. -/
theorem onlineMVPCommittedPlanningRow_eq_actualBatch
    {Row : Type*} [Nonempty Outcome] [DecidableEq Row]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row)
    (hN : 0 < (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r) :
    onlineMVPCommittedPlanningRow rowAt nextAt n r =
      FiniteDistribution.empiricalRow
        (onlineMVPSourceBatchList (onlineMVPRowVisitList rowAt nextAt n r)).length
        (by rw [onlineMVPActualBatch_length_eq_committedStored]; exact hN)
        (fun i => (onlineMVPSourceBatchList
          (onlineMVPRowVisitList rowAt nextAt n r)).get i) := by
  classical
  let st := onlineMVPCommittedTablesRun rowAt nextAt n
  let xs := onlineMVPRowVisitList rowAt nextAt n r
  let batch := onlineMVPSourceBatchList xs
  have hlen : batch.length = st.base.stored r := by
    simpa [batch, st] using
      onlineMVPActualBatch_length_eq_committedStored rowAt nextAt n r
  have hhist : ∀ x, st.committed r x = batch.count x := by
    intro x
    simpa [st, batch, xs, onlineMVPSourceBatchHistogram] using
      onlineMVPCommittedTablesRun_committed_eq_sourceBatchHistogram rowAt nextAt n r x
  have hbatchPos : 0 < batch.length := by rw [hlen]; exact hN
  have hprob : ∀ x, (onlineMVPCommittedPlanningRow rowAt nextAt n r).prob x =
      (FiniteDistribution.empiricalRow batch.length (by omega : 0 < batch.length)
        (fun i => batch.get i)).prob x := by
    intro x
    have hleft : (onlineMVPCommittedPlanningRow rowAt nextAt n r).prob x =
        (st.base.stored r : ℝ)⁻¹ * (batch.count x : ℝ) := by
      unfold onlineMVPCommittedPlanningRow
      dsimp
      rw [dif_pos hN]
      simp only [onlineMVPCommittedHistogramDistribution, onlineMVPHistogramDistribution]
      rw [hhist x]
    rw [hleft, onlineMVP_empiricalRow_prob_eq_count batch x hbatchPos, ← hlen]
  exact onlineMVP_finiteDistribution_ext _ _ hprob

/-- Zero stored mass uses the source uniform initialization, kept separate from
the positive-count empirical-row equality. -/
theorem onlineMVPCommittedPlanningRow_eq_uniform_of_zero
    {Row : Type*} [Nonempty Outcome] [DecidableEq Row]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row)
    (hN : (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r = 0) :
    onlineMVPCommittedPlanningRow rowAt nextAt n r = onlineMVPUniformDistribution := by
  have hnot : ¬ 0 < (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r := by omega
  unfold onlineMVPCommittedPlanningRow
  dsimp
  rw [dif_neg hnot]

/-- The source's completed-history planning row is exactly the row produced
from retained MVP data: the actual dyadic batch when stored count is positive,
and uniform initialization when it is zero. -/
theorem onlineMVPActualPlanningStage_row_eq_committed
    {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
    {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State)
    (n : ℕ) (h : Fin H) (s : State) (a : Action) :
    onlineObservedPlanningRow (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
      onlineMVPCommittedPlanningRow rowAt nextAt n (h, (s, a)) := by
  let r : Fin H × State × Action := (h, (s, a))
  let batch := onlineMVPSourceBatchList (onlineMVPRowVisitList rowAt nextAt n r)
  by_cases hN : 0 < (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r
  · have hlen : batch.length =
        (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r := by
      simpa [batch, r] using onlineMVPActualBatch_length_eq_committedStored rowAt nextAt n r
    have hpos : 0 < batch.length := by rw [hlen]; exact hN
    have hpos' : 0 < ((onlineMVPActualPlanningStage E rowAt nextAt n h).observations s a).length := by
      simpa [onlineMVPActualPlanningStage, batch, r] using hpos
    have hobs : onlineObservedPlanningRow
        (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
        FiniteDistribution.empiricalRow batch.length hpos (fun i => batch.get i) := by
      simpa [onlineMVPActualPlanningStage, batch, r] using
        onlineObservedPlanningRow_positive
          (onlineMVPActualPlanningStage E rowAt nextAt n h) s a hpos'
    rw [hobs]
    simpa [batch, r] using
      (onlineMVPCommittedPlanningRow_eq_actualBatch rowAt nextAt n r hN).symm
  · have hzero : (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r = 0 := by
      omega
    have hlen : batch.length = 0 := by
      simpa [batch, r, hzero] using onlineMVPActualBatch_length_eq_committedStored rowAt nextAt n r
    have hobs : onlineObservedPlanningRow
        (onlineMVPActualPlanningStage E rowAt nextAt n h) s a =
        onlineMVPUniformDistribution := by
      apply onlineMVP_finiteDistribution_ext
      intro x
      simp [onlineObservedPlanningRow, onlineMVPActualPlanningStage, batch, r, hlen,
        onlineUniformInitialRow, onlineMVPUniformDistribution]
    rw [hobs, onlineMVPCommittedPlanningRow_eq_uniform_of_zero rowAt nextAt n r hzero]

end StatisticalRL.OnlineRL
