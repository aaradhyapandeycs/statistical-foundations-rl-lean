import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPFixedProfileZeroTerminal
import Formalization.Online.Regret.MVP.MVPActualProfiles
import Mathlib.Data.List.OfFn

/-! A deterministic bridge from a source profile index to the exact finite
stack slice used by the committed row batch. This remains a pathwise helper;
it does not identify an auxiliary fixed-profile value with the deployed value
or transport an event between probability laws. -/

namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance profileBatchStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance profileBatchActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Number of source observations assigned to profile level `j`. -/
def onlineMVPProfileBatchSize (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then 1 else 2 ^ (j - 2)

/-- Zero-based beginning of the source batch in a row's expanded stack. -/
def onlineMVPProfileBatchStart (j : ℕ) : ℕ :=
  if j < 2 then 0 else 2 ^ (j - 2)

/-- A generic list slice is the `ofFn` list of its indexed entries. -/
theorem onlineMVP_list_take_drop_eq_ofFn
    {α : Type*} (xs : List α) (start size : ℕ)
    (hbound : start + size ≤ xs.length) :
    (xs.take (start + size)).drop start =
      List.ofFn (fun i : Fin size => xs.get ⟨start + i.val, by omega⟩) := by
  have hlen : ((xs.take (start + size)).drop start).length = size := by
    simp only [List.length_drop, List.length_take]
    omega
  apply List.ext_getElem?'
  intro i hi
  have his : i < size := by
    simpa [hlen] using hi
  have hiL : i < ((xs.take (start + size)).drop start).length := by
    simpa only [hlen] using his
  have hiR : i < (List.ofFn (fun i : Fin size =>
      xs.get ⟨start + i.val, by omega⟩)).length := by
    simpa using his
  simp only [List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hiR,
    List.getElem_drop, List.getElem_take, List.getElem_ofFn]
  congr 1

/-- The committed source batch has the source profile's stack-slice shape,
assuming the profile count and slice endpoints agree with its retained
counter. The profile index is arbitrary here; the actual model bridge below
supplies these arithmetic equalities from the operational counters. -/
theorem onlineMVPSourceBatchList_eq_profile_slice
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (xs : List Outcome) (j : ℕ)
    (hsize : onlineMVPProfileBatchSize j = onlineMVPStoredCount xs.length)
    (hstart : onlineMVPProfileBatchStart j = onlineMVPSourceBatchStart xs.length)
    (hend : onlineMVPSourceBatchStart xs.length + onlineMVPProfileBatchSize j =
      onlineMVPSourceBatchEnd xs.length) :
    onlineMVPSourceBatchList xs =
      List.ofFn (fun i : Fin (onlineMVPProfileBatchSize j) =>
        xs.get ⟨onlineMVPProfileBatchStart j + i.val, by
          have hbound : onlineMVPProfileBatchStart j +
              onlineMVPProfileBatchSize j ≤ xs.length := by
            rw [hstart, hend]
            exact onlineMVPSourceBatchEnd_le xs.length
          omega⟩) := by
  rw [onlineMVPSourceBatchList]
  calc
    (List.take (onlineMVPSourceBatchEnd xs.length) xs).drop
        (onlineMVPSourceBatchStart xs.length) =
      List.ofFn (fun i : Fin (onlineMVPProfileBatchSize j) =>
        xs.get ⟨onlineMVPSourceBatchStart xs.length + i.val, by
          have hbound : onlineMVPSourceBatchStart xs.length +
              onlineMVPProfileBatchSize j ≤ xs.length := by
            rw [hend]
            exact onlineMVPSourceBatchEnd_le xs.length
          omega⟩) := by
        conv_lhs => rw [← hend]
        apply onlineMVP_list_take_drop_eq_ofFn
        rw [hend]
        exact onlineMVPSourceBatchEnd_le xs.length
    _ = List.ofFn (fun i : Fin (onlineMVPProfileBatchSize j) =>
        xs.get ⟨onlineMVPProfileBatchStart j + i.val, by
          have hbound : onlineMVPProfileBatchStart j +
              onlineMVPProfileBatchSize j ≤ xs.length := by
            rw [hstart, hend]
            exact onlineMVPSourceBatchEnd_le xs.length
          omega⟩) := by
        congr 1
        funext i
        congr 1
        apply Fin.ext
        simp [hstart]

/-- The profile parameters are exactly the retained source slice endpoints.
The small-count cases are the separate empty/uniform and first-sample
branches; later profiles are the preceding dyadic block. -/
theorem onlineMVPProfileBatch_parameters (n : ℕ) :
    onlineMVPProfileBatchSize (sourceMVPProfileIndex n) = onlineMVPStoredCount n ∧
    onlineMVPProfileBatchStart (sourceMVPProfileIndex n) = onlineMVPSourceBatchStart n ∧
    onlineMVPProfileBatchStart (sourceMVPProfileIndex n) +
        onlineMVPProfileBatchSize (sourceMVPProfileIndex n) =
      onlineMVPSourceBatchEnd n := by
  by_cases hzero : n = 0
  · subst n
    simp [onlineMVPProfileBatchSize, onlineMVPProfileBatchStart,
      sourceMVPProfileIndex, onlineMVPStoredCount, onlineMVPRowCountState,
      onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd]
  · by_cases hone : n = 1
    · subst n
      decide
    · have hn : 2 ≤ n := by omega
      have hj : sourceMVPProfileIndex n = Nat.log2 n + 1 := by
        simp [sourceMVPProfileIndex, hzero]
      have hlogpos : Nat.log2 n ≠ 0 := by
        have hlog : 1 ≤ Nat.log2 n := by
          apply (Nat.le_log2 (by omega : n ≠ 0)).2
          exact hn
        omega
      have hcount : onlineMVPStoredCount n = 2 ^ (Nat.log2 n - 1) := by
        rw [onlineMVP_storedCount_eq_profile_batch n, hj]
        simp [hn, hlogpos]
      have hexp : Nat.log2 n + 1 - 2 = Nat.log2 n - 1 := by omega
      have hsize : onlineMVPProfileBatchSize (sourceMVPProfileIndex n) =
          onlineMVPStoredCount n := by
        rw [hj]
        rw [onlineMVPProfileBatchSize]
        have hidx0 : Nat.log2 n + 1 ≠ 0 := by omega
        have hidx1 : Nat.log2 n + 1 ≠ 1 := by omega
        rw [if_neg hidx0, if_neg hidx1, hexp, hcount]
      have hstart : onlineMVPProfileBatchStart (sourceMVPProfileIndex n) =
          onlineMVPSourceBatchStart n := by
        rw [hj]
        have hidx : ¬ Nat.log2 n + 1 < 2 := by omega
        rw [onlineMVPProfileBatchStart, if_neg hidx,
          onlineMVPSourceBatchStart, if_neg (by omega : ¬ n < 2), hcount, hexp]
      refine ⟨hsize, hstart, ?_⟩
      rw [hstart, hsize, onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd,
        if_neg (by omega : ¬ n < 2), if_neg (by omega : ¬ n < 2), hcount]
      omega

theorem onlineMVPProfileBatch_index_lt (n : ℕ)
    (i : Fin (onlineMVPProfileBatchSize (sourceMVPProfileIndex n))) :
    onlineMVPProfileBatchStart (sourceMVPProfileIndex n) + i.val < n := by
  have hparams := onlineMVPProfileBatch_parameters n
  calc
    onlineMVPProfileBatchStart (sourceMVPProfileIndex n) + i.val <
        onlineMVPProfileBatchStart (sourceMVPProfileIndex n) +
          onlineMVPProfileBatchSize (sourceMVPProfileIndex n) := by omega
    _ = onlineMVPSourceBatchEnd n := hparams.2.2
    _ ≤ n := onlineMVPSourceBatchEnd_le n

theorem onlineMVPActualProfileBatchIndex_lt_K
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K * H) (r : OnlineMDPRow State Action H)
    (i : Fin (onlineMVPProfileBatchSize (sourceMVPProfileIndex
      (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r).length))) :
    onlineMVPProfileBatchStart (sourceMVPProfileIndex
      (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r).length) +
        i.val < K := by
  have hprefix := onlineMVPActualStackHistory_rowCount_le_K hH initial fallback
    planner data n hn r
  exact lt_of_lt_of_le (onlineMVPProfileBatch_index_lt _ i) hprefix

/-- At any actual-stack prefix, the source's committed batch is exactly the
selected coordinate slice of that row's expanded successor stack. This is a
pathwise equality and makes no independence or random-count assumption. -/
theorem onlineMVPActualSourceBatch_eq_stackProfile
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K * H) (r : OnlineMDPRow State Action H) :
    let xs := onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback planner data n) r
    onlineMVPSourceBatchList xs =
      List.ofFn (fun i : Fin (onlineMVPProfileBatchSize (sourceMVPProfileIndex xs.length)) =>
        data (r, ⟨onlineMVPProfileBatchStart (sourceMVPProfileIndex xs.length) + i.val, by
          exact onlineMVPActualProfileBatchIndex_lt_K hH initial fallback planner data n hn r i⟩)) := by
  dsimp
  let xs := onlineRowOutcomes
    (onlineMVPActualStackHistory hH initial fallback planner data n) r
  have hparams := onlineMVPProfileBatch_parameters xs.length
  have hendSource : onlineMVPSourceBatchStart xs.length +
      onlineMVPProfileBatchSize (sourceMVPProfileIndex xs.length) =
        onlineMVPSourceBatchEnd xs.length := by
    rw [← hparams.2.1]
    exact hparams.2.2
  rw [onlineMVPSourceBatchList_eq_profile_slice xs (sourceMVPProfileIndex xs.length)
    hparams.1 hparams.2.1 hendSource]
  congr 1
  funext i
  let ix : Fin xs.length := ⟨onlineMVPProfileBatchStart (sourceMVPProfileIndex xs.length) + i.val,
    onlineMVPProfileBatch_index_lt xs.length i⟩
  have hstack := onlineMVPActualStackHistory_rowNth_eq_stack hH initial fallback
    planner data n hn r ix
  exact hstack

end StatisticalRL.OnlineRL
