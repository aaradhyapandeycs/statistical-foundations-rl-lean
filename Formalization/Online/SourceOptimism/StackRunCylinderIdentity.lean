import Formalization.Online.SourceOptimism.VisitCoordinateDistinct
import Mathlib.Data.List.TakeDrop
import Formalization.Online.SourceOptimism.SuccessorStackPrefix

/-! Exact deterministic adaptive run-event
identity and fixed transcript count conversion; no path-law equality assumed. -/
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [DecidableEq Row]

/-- Earlier prefixes of the run are exactly the corresponding history takes. -/
theorem onlineStackHistory_take
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (n k : ℕ) (hk : k≤n) :
    (onlineStackHistory choose stream n).take k=onlineStackHistory choose stream k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases hkn : k≤n
    · rw [onlineStackHistory]
      change (onlineStackHistory choose stream n ++ [_]).take k = _
      rw [List.take_append_of_le_length (by
        simpa only [onlineStackHistory_length] using hkn)]
      exact ih k hkn
    · have hks : k=n+1 := by omega
      subst k
      simpa only [onlineStackHistory_length] using
        (List.take_length (l := onlineStackHistory choose stream (n + 1)))

/-- A fixed transcript's records must be exactly the causal next row/read
at each of its prefixes. This predicate is explicit, with no run or probability
on its right-hand side. -/
def onlineTranscriptSteps
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (history : List (Row × Outcome)) : Prop :=
  ∀ j : Fin history.length,
    history.get j =
      (choose (history.take j.val),stream (choose (history.take j.val))
        (onlineRowOutcomes (history.take j.val) (choose (history.take j.val))).length)

/-- The adaptive run's exact history event equals the explicit intersection
of its causal transcript coordinate constraints. This is purely pathwise. -/
theorem onlineStackHistory_eq_iff_transcriptSteps
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (history : List (Row × Outcome)) :
    onlineStackHistory choose stream history.length=history ↔
      onlineTranscriptSteps choose stream history := by
  constructor
  · intro heq j
    have hp : onlineStackHistory choose stream j.val=history.take j.val := by
      have h := congrArg (List.take j.val) heq
      rw [onlineStackHistory_take choose stream history.length j.val j.isLt.le] at h
      exact h
    have hpnext : onlineStackHistory choose stream (j.val+1)=history.take (j.val+1) := by
      have h := congrArg (List.take (j.val+1)) heq
      rw [onlineStackHistory_take choose stream history.length (j.val+1) (by omega)] at h
      exact h
    rw [onlineStackHistory,hp] at hpnext
    rw [← List.take_concat_get' history j.val j.isLt] at hpnext
    have hs := List.append_cancel_left hpnext
    have hpair : (choose (history.take j.val),
        stream (choose (history.take j.val))
          (onlineRowOutcomes (history.take j.val) (choose (history.take j.val))).length) =
        history.get j := by simpa using hs
    exact hpair.symm
  · intro hsteps
    have hp : ∀ k, k≤history.length →
        onlineStackHistory choose stream k=history.take k := by
      intro k
      induction k with
      | zero => intro _; simp [onlineStackHistory]
      | succ k ih =>
        intro hk
        have hklt : k<history.length := by omega
        have hj := hsteps ⟨k,hklt⟩
        rw [onlineStackHistory,ih (by omega)]
        rw [← hj]
        exact List.take_concat_get' history k hklt
    simpa using hp history.length le_rfl

/-- Pure row consistency is fixed before the stream values are considered. -/
def onlineTranscriptRowsConsistent
    (choose : List (Row × Outcome) → Row) (history : List (Row × Outcome)) : Prop :=
  ∀ j : Fin history.length, (history.get j).1=choose (history.take j.val)

/-- Separate the deterministic row choices from the fixed coordinate-value
constraints. This exposes the cylinder suitable for product mass evaluation. -/
theorem onlineTranscriptSteps_iff_rows_and_coordinates
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (history : List (Row × Outcome)) :
    onlineTranscriptSteps choose stream history ↔
      onlineTranscriptRowsConsistent choose history ∧
      ∀ j : Fin history.length,
        stream (history.get j).1
          (onlineRowOutcomes (history.take j.val) (history.get j).1).length =
            (history.get j).2 := by
  constructor
  · intro hs
    have hr : onlineTranscriptRowsConsistent choose history :=
      fun j => congrArg Prod.fst (hs j)
    refine ⟨hr,fun j => ?_⟩
    rw [hr j]
    exact (congrArg Prod.snd (hs j)).symm
  · rintro ⟨hr,hx⟩ j
    apply Prod.ext
    · exact hr j
    · have h := hx j
      rw [hr j] at h
      exact h.symm

/-- A fixed transcript's row-prefix list count equals the earlier-episode
counting API whenever rowAt enumerates those fixed transcript rows. -/
theorem onlineTranscript_rowCount_eq_visitCount
    (history : List (Row × Outcome)) (rowAt : ℕ → Row)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1)
    (k : ℕ) (hk : k≤history.length) (r : Row) :
    (onlineRowOutcomes (history.take k) r).length=onlineVisitCount rowAt k r := by
  induction k with
  | zero => simp [onlineRowOutcomes,onlineVisitCount_zero]
  | succ k ih =>
    have hklt : k<history.length := by omega
    rw [← List.take_concat_get' history k hklt,onlineRowOutcomes_append_one,
      List.length_append,ih (by omega),onlineVisitCount_succ]
    rw [hrows ⟨k,hklt⟩]
    split_ifs <;> simp_all

end StatisticalRL.OnlineRL
