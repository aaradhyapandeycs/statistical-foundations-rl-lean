import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPCommittedHistogram
import Formalization.Online.Regret.MVP.Model.OnlineMVPRowBatchIdentity
import Formalization.Online.Regret.MVP.OnlineMVPStoredClosedForm
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source batch indexing for the committed row histogram. The positive-count
batch is the dyadic source interval; zero-count initialization is treated
separately and never normalized by a zero sample count. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

theorem onlineMVPRowBatchStateRun_scalar {xs : List Outcome} :
    (onlineMVPRowBatchStateRun xs).total = xs.length ∧
      ((∑ y : Outcome, (onlineMVPRowBatchStateRun xs).pending y),
        (onlineMVPRowBatchStateRun xs).stored) =
        onlineMVPRowCountState xs.length := by
  induction xs using List.reverseRecOn with
  | nil => simp [onlineMVPRowBatchStateRun, onlineMVPRowBatchStateInit,
      onlineMVPRowCountState]
  | append_singleton xs x ih =>
      rw [onlineMVPRowBatchStateRun_append_one]
      simp only [List.length_append, List.length_singleton, Nat.add_one]
      have htrigger :
          onlineMVPRowTrigger ((onlineMVPRowBatchStateRun xs).total + 1) ↔
            onlineMVPRowTrigger (xs.length + 1) := by
        rw [ih.1]
      constructor
      · by_cases hc : onlineMVPRowTrigger (xs.length + 1)
        · simp [onlineMVPRowBatchStateStep, htrigger, hc, ih.1]
        · simp [onlineMVPRowBatchStateStep, htrigger, hc, ih.1]
      · by_cases hc : onlineMVPRowTrigger (xs.length + 1)
        · have hfirst : (∑ y, (onlineMVPRowBatchStateRun xs).pending y) =
              (onlineMVPRowCountState xs.length).1 := by
            simpa using congrArg Prod.fst ih.2
          have hsum := onlineMVP_pendingAfter_sum (onlineMVPRowBatchStateRun xs).pending x
          simp [onlineMVPRowBatchStateStep, onlineMVPRowCountState, htrigger,
            hc, hsum, hfirst]
        · have hfirst : (∑ y, (onlineMVPRowBatchStateRun xs).pending y) =
              (onlineMVPRowCountState xs.length).1 := by
            simpa using congrArg Prod.fst ih.2
          have hsecond : (onlineMVPRowBatchStateRun xs).stored =
              (onlineMVPRowCountState xs.length).2 := by
            simpa using congrArg Prod.snd ih.2
          have hsum := onlineMVP_pendingAfter_sum (onlineMVPRowBatchStateRun xs).pending x
          simp [onlineMVPRowBatchStateStep, onlineMVPRowCountState, htrigger, hc,
            hsum, hfirst, hsecond]

theorem onlineMVPSourceBatchEnd_eq_logPower {n : ℕ} (hn : 2 ≤ n) :
    onlineMVPSourceBatchEnd n = 2 ^ Nat.log2 n := by
  have hlog : 1 ≤ Nat.log2 n := by
    apply (Nat.le_log2 (by omega : n ≠ 0)).2
    omega
  have hsub : Nat.log2 n - 1 + 1 = Nat.log2 n := by omega
  rw [onlineMVPSourceBatchEnd, if_neg (by omega : ¬ n < 2),
    onlineMVP_storedCount_closedForm, if_neg (by omega : ¬ n < 2)]
  calc
    2 * 2 ^ (Nat.log2 n - 1) = 2 ^ (Nat.log2 n - 1) * 2 := Nat.mul_comm _ _
    _ = 2 ^ (Nat.log2 n - 1 + 1) := by rw [Nat.pow_succ]
    _ = 2 ^ Nat.log2 n := by rw [hsub]

theorem onlineMVPSourceBatchEnd_le (n : ℕ) : onlineMVPSourceBatchEnd n ≤ n := by
  by_cases hn : n < 2
  · simp [onlineMVPSourceBatchEnd, hn]
  · have hn0 : n ≠ 0 := by omega
    rw [onlineMVPSourceBatchEnd_eq_logPower (by omega)]
    exact onlineMVP_floorPower_le n hn0

theorem onlineMVPSourceBatchEnd_eq_succ_of_trigger {n : ℕ}
    (hc : onlineMVPRowTrigger (n + 1)) :
    onlineMVPSourceBatchEnd (n + 1) = n + 1 := by
  by_cases hsmall : n + 1 < 2
  · have hn : n = 0 := by omega
    subst n
    norm_num [onlineMVPSourceBatchEnd]
  · have hpos : 2 ≤ n + 1 := by omega
    rw [onlineMVPSourceBatchEnd_eq_logPower (n := n + 1) hpos]
    obtain ⟨j, hj⟩ := (onlineMVP_trigger_iff_power (n + 1)).1 hc
    rw [hj, Nat.log2_two_pow]

theorem onlineMVPSourceBatchEnd_stable_of_not_trigger {n : ℕ}
    (hc : ¬ onlineMVPRowTrigger (n + 1)) :
    onlineMVPSourceBatchEnd (n + 1) = onlineMVPSourceBatchEnd n := by
  by_cases hn : n < 2
  · interval_cases n
    · exfalso
      exact hc (by decide)
    · exfalso
      exact hc (by decide)
  · have hn2 : 2 ≤ n := by omega
    have hst : onlineMVPStoredCount (n + 1) = onlineMVPStoredCount n := by
      unfold onlineMVPStoredCount
      cases n with
      | zero => omega
      | succ n => simp [onlineMVPRowCountState, hc]
    rw [onlineMVPSourceBatchEnd, onlineMVPSourceBatchEnd, if_neg (by omega),
      if_neg (by omega), hst]

theorem onlineMVPSourceBatchStart_stable_of_not_trigger {n : ℕ}
    (hc : ¬ onlineMVPRowTrigger (n + 1)) :
    onlineMVPSourceBatchStart (n + 1) = onlineMVPSourceBatchStart n := by
  by_cases hn : n < 2
  · interval_cases n
    · exfalso; exact hc (by decide)
    · exfalso; exact hc (by decide)
  · have hst : onlineMVPStoredCount (n + 1) = onlineMVPStoredCount n := by
      unfold onlineMVPStoredCount
      cases n with
      | zero => omega
      | succ n => simp [onlineMVPRowCountState, hc]
    rw [onlineMVPSourceBatchStart, onlineMVPSourceBatchStart,
      if_neg (by omega), if_neg (by omega), hst]

theorem onlineMVP_log2_pow_sub_one (j : ℕ) (hj : 2 ≤ j) :
    Nat.log2 (2^j - 1) = j - 1 := by
  have hp : 2^j = 2^(j-1) + 2^(j-1) := by
    have he : j = (j-1)+1 := by omega
    rw [he, Nat.pow_succ]
    simp [Nat.mul_two]
  have hp0 : 0 < 2^(j-1) := by positivity
  have hlo : 2^(j-1) ≤ 2^j - 1 := by
    rw [hp]
    omega
  have hhi : 2^j - 1 < 2^((j-1)+1) := by
    have he : (j-1)+1 = j := by omega
    have hpj0 : 0 < 2^j := by positivity
    rw [he]
    exact Nat.sub_lt hpj0 (by decide)
  have hlog := onlineMVP_log2_eq_of_dyadic_bounds (2^j - 1) (j-1) hlo hhi
  exact hlog

theorem onlineMVPSourceBatchStart_eq_end_of_trigger {n : ℕ}
    (hc : onlineMVPRowTrigger (n + 1)) :
    onlineMVPSourceBatchStart (n + 1) = onlineMVPSourceBatchEnd n := by
  obtain ⟨j, hj⟩ := (onlineMVP_trigger_iff_power (n+1)).1 hc
  by_cases hj0 : j = 0
  · subst j
    have hn : n = 0 := by omega
    subst n
    norm_num [onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd]
  · by_cases hj1 : j = 1
    · subst j
      have hn : n = 1 := by omega
      subst n
      decide
    · have hj2 : 2 ≤ j := by omega
      have hpowge4 : 4 ≤ 2^j := by
        have hjdecomp : j = (j-2)+2 := by omega
        rw [hjdecomp, pow_add]
        have hx : 0 < 2^(j-2) := by positivity
        norm_num [pow_succ]
        nlinarith
      have hn : n = 2^j - 1 := by omega
      rw [hn, onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd]
      have hlog : Nat.log2 (2^j - 1) = j - 1 :=
        onlineMVP_log2_pow_sub_one j hj2
      have hpowred : 2^j - 1 + 1 = 2^j := by omega
      have hlogplus : Nat.log2 (2^j - 1 + 1) = j := by
        rw [hpowred, Nat.log2_two_pow]
      have hnplus : ¬ 2^j - 1 + 1 < 2 := by rw [hpowred]; omega
      have hn : ¬ 2^j - 1 < 2 := by omega
      simp [onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd,
        onlineMVP_storedCount_closedForm, hnplus, hn, hlogplus, hlog]
      have hsub : j - 1 - 1 + 1 = j - 1 := by omega
      calc
        2 ^ (j - 1) = 2 ^ (j - 1 - 1 + 1) := by rw [hsub]
        _ = 2 * 2 ^ (j - 1 - 1) := by rw [Nat.pow_succ]; omega

/-- The pending histogram after `n` observations is exactly the suffix after
the end of the currently committed dyadic batch. -/
theorem onlineMVPRowBatchStateRun_pending_eq_suffix {xs : List Outcome} (x : Outcome) :
    (onlineMVPRowBatchStateRun xs).pending x =
      ((xs.drop (onlineMVPSourceBatchEnd xs.length)).count x) := by
  induction xs using List.reverseRecOn with
  | nil => simp [onlineMVPRowBatchStateRun, onlineMVPRowBatchStateInit,
      onlineMVPSourceBatchEnd]
  | append_singleton xs y ih =>
      rw [onlineMVPRowBatchStateRun_append_one]
      simp only [List.length_append, List.length_singleton, Nat.add_one]
      have htotal : (onlineMVPRowBatchStateRun xs).total = xs.length :=
        onlineMVPRowBatchStateRun_scalar.1
      have htrigger :
          onlineMVPRowTrigger ((onlineMVPRowBatchStateRun xs).total + 1) ↔
            onlineMVPRowTrigger (xs.length + 1) := by rw [htotal]
      by_cases hc : onlineMVPRowTrigger (xs.length + 1)
      · rw [onlineMVPSourceBatchEnd_eq_succ_of_trigger hc]
        simp [onlineMVPRowBatchStateStep, htrigger, hc, htotal]
      · have hstable := onlineMVPSourceBatchEnd_stable_of_not_trigger hc
        have hendle := onlineMVPSourceBatchEnd_le xs.length
        rw [onlineMVPSourceBatchEnd_stable_of_not_trigger hc]
        rw [List.drop_append_of_le_length hendle, List.count_append, ← ih]
        by_cases hxy : x = y
        · subst y
          simp [onlineMVPRowBatchStateStep, hc, htotal, List.count]
        · simp [onlineMVPRowBatchStateStep, hc, htotal, hxy, List.count]
          exact fun hyx => hxy hyx.symm

/-- Histogram of the actual source batch: for the first profile it is the
first row visit; for later profiles it is the preceding half-power block. -/
def onlineMVPSourceBatchHistogram (xs : List Outcome) (x : Outcome) : ℕ :=
  (onlineMVPSourceBatchList xs).count x

theorem onlineMVPSourceBatchList_append_trigger {xs : List Outcome} (y : Outcome)
    (hc : onlineMVPRowTrigger (xs.length + 1)) :
    onlineMVPSourceBatchList (xs ++ [y]) =
      xs.drop (onlineMVPSourceBatchEnd xs.length) ++ [y] := by
  have hstart := onlineMVPSourceBatchStart_eq_end_of_trigger hc
  have hend := onlineMVPSourceBatchEnd_eq_succ_of_trigger hc
  have hle := onlineMVPSourceBatchEnd_le xs.length
  unfold onlineMVPSourceBatchList
  simp only [List.length_append, List.length_singleton, Nat.add_one]
  rw [hend, hstart]
  rw [List.take_append]
  have htake : List.take (xs.length + 1 - xs.length) [y] = [y] := by
    rw [show xs.length + 1 - xs.length = 1 by omega]
    rfl
  rw [htake, List.take_of_length_le (by omega : xs.length ≤ xs.length + 1)]
  rw [List.drop_append_of_le_length hle]

theorem onlineMVPSourceBatchList_append_not_trigger {xs : List Outcome}
    (y : Outcome) (hc : ¬ onlineMVPRowTrigger (xs.length + 1)) :
    onlineMVPSourceBatchList (xs ++ [y]) = onlineMVPSourceBatchList xs := by
  have hstart := onlineMVPSourceBatchStart_stable_of_not_trigger hc
  have hend := onlineMVPSourceBatchEnd_stable_of_not_trigger hc
  have hle := onlineMVPSourceBatchEnd_le xs.length
  unfold onlineMVPSourceBatchList
  simp only [List.length_append, List.length_singleton, Nat.add_one]
  rw [hstart, hend, List.take_append_of_le_length hle]

theorem onlineMVPRowBatchStateRun_committed_eq_sourceBatchHistogram
    {xs : List Outcome} (x : Outcome) :
    (onlineMVPRowBatchStateRun xs).committed x = onlineMVPSourceBatchHistogram xs x := by
  induction xs using List.reverseRecOn with
  | nil => simp [onlineMVPRowBatchStateRun, onlineMVPRowBatchStateInit,
      onlineMVPSourceBatchHistogram, onlineMVPSourceBatchList,
      onlineMVPSourceBatchEnd, onlineMVPSourceBatchStart]
  | append_singleton xs y ih =>
      rw [onlineMVPRowBatchStateRun_append_one]
      have htotal : (onlineMVPRowBatchStateRun xs).total = xs.length :=
        onlineMVPRowBatchStateRun_scalar.1
      have htrigger :
          onlineMVPRowTrigger ((onlineMVPRowBatchStateRun xs).total + 1) ↔
            onlineMVPRowTrigger (xs.length + 1) := by rw [htotal]
      by_cases hc : onlineMVPRowTrigger (xs.length + 1)
      · change (onlineMVPRowBatchStateStep (onlineMVPRowBatchStateRun xs) y).committed x =
          (onlineMVPSourceBatchList (xs ++ [y])).count x
        rw [onlineMVPSourceBatchList_append_trigger y hc]
        change (onlineMVPRowBatchStateStep (onlineMVPRowBatchStateRun xs) y).committed x =
          (xs.drop (onlineMVPSourceBatchEnd xs.length) ++ [y]).count x
        have hpend := onlineMVPRowBatchStateRun_pending_eq_suffix (xs := xs) x
        rw [List.count_append, ← hpend]
        simp only [List.count_singleton]
        have hpos : onlineMVPRowTrigger ((onlineMVPRowBatchStateRun xs).total + 1) :=
          htrigger.mpr hc
        simp only [onlineMVPRowBatchStateStep, dif_pos hpos]
        by_cases hxy : x = y
        · subst y; simp
        · simp [hxy, Ne.symm hxy]
      · change (onlineMVPRowBatchStateStep (onlineMVPRowBatchStateRun xs) y).committed x =
          (onlineMVPSourceBatchList (xs ++ [y])).count x
        rw [onlineMVPSourceBatchList_append_not_trigger y hc]
        change (onlineMVPRowBatchStateStep (onlineMVPRowBatchStateRun xs) y).committed x =
          onlineMVPSourceBatchHistogram xs x
        simpa [onlineMVPRowBatchStateStep, htrigger, hc, htotal,
          onlineMVPSourceBatchHistogram] using ih

theorem onlineMVPSourceBatchList_length (xs : List Outcome) :
    (onlineMVPSourceBatchList xs).length = onlineMVPStoredCount xs.length := by
  by_cases hn : xs.length < 2
  · have hstored : onlineMVPStoredCount xs.length = xs.length := by
      rw [onlineMVP_storedCount_closedForm]
      simp [hn]
    simp [onlineMVPSourceBatchList, onlineMVPSourceBatchStart,
      onlineMVPSourceBatchEnd, hn, List.length_drop, List.length_take,
      Nat.min_eq_left (by omega : xs.length ≤ xs.length), hstored]
  · have hn2 : 2 ≤ xs.length := by omega
    have hle := onlineMVPSourceBatchEnd_le xs.length
    have hend : onlineMVPSourceBatchEnd xs.length =
        2 * onlineMVPStoredCount xs.length := by
      simp [onlineMVPSourceBatchEnd, hn]
    simp only [onlineMVPSourceBatchList, onlineMVPSourceBatchStart,
      onlineMVPSourceBatchEnd, if_neg hn, List.length_drop, List.length_take]
    rw [Nat.min_eq_left (by simpa [hend] using hle)]
    omega

theorem onlineMVPCommittedTablesRun_committed_eq_sourceBatchHistogram
    {Row Outcome : Type*} [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) (x : Outcome) :
    (onlineMVPCommittedTablesRun rowAt nextAt n).committed r x =
      onlineMVPSourceBatchHistogram (onlineMVPRowVisitList rowAt nextAt n r) x := by
  have hrow := onlineMVPCommittedTablesRun_row_eq_visitList rowAt nextAt n r
  have hfield := congrArg (fun s : OnlineMVPRowBatchState Outcome => s.committed x) hrow
  calc
    (onlineMVPCommittedTablesRun rowAt nextAt n).committed r x =
        (onlineMVPRowBatchStateRun (onlineMVPRowVisitList rowAt nextAt n r)).committed x := by
          simpa [onlineMVPCommittedRowView] using hfield.symm
    _ = onlineMVPSourceBatchHistogram (onlineMVPRowVisitList rowAt nextAt n r) x :=
      onlineMVPRowBatchStateRun_committed_eq_sourceBatchHistogram x

end StatisticalRL.OnlineRL
