import Formalization.Online.SourceOptimism.SequentialEpisodeLaw
import Formalization.Online.SourceOptimism.TranscriptRowDefinitions

/-! Direct sequential paths construct consistent
transcripts injectively; no probability or coupling assumption is supplied. -/
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome] [DecidableEq Row]

/-- A causal chosen-row extension preserves transcript consistency. -/
theorem onlineTranscriptRowsConsistent_append_chosen
    (choose : List (Row × Outcome) → Row) (history : List (Row × Outcome))
    (hr : onlineTranscriptRowsConsistent choose history) (x : Outcome) :
    onlineTranscriptRowsConsistent choose (history++[(choose history,x)]) := by
  intro j
  by_cases hj : j.val<history.length
  · have h := hr ⟨j.val,hj⟩
    simpa [List.get_eq_getElem,List.getElem_append,hj,List.take_append,
      Nat.sub_eq_zero_of_le hj.le] using h
  · have heq : j.val=history.length := by
      have hlt := j.isLt
      simp only [List.length_append,List.length_singleton] at hlt
      omega
    simp [List.get_eq_getElem,List.getElem_append,heq]

/-- Actual reconstruction preserves every previously consistent row choice. -/
theorem onlineSequentialPathHistory_rows_consistent
    (choose : List (Row × Outcome) → Row) (n : ℕ)
    (history : List (Row × Outcome)) (hr : onlineTranscriptRowsConsistent choose history)
    (path : OnlineOutcomePath Outcome n) :
    onlineTranscriptRowsConsistent choose (onlineSequentialPathHistory choose n history path) := by
  induction n generalizing history with
  | zero => exact hr
  | succ n ih =>
    exact ih (history++[(choose history,path.2.1)])
      (onlineTranscriptRowsConsistent_append_chosen choose history hr path.2.1) path.2.2

/-- Reconstructed successor observations are exactly the direct outcome path. -/
theorem onlineSequentialPathHistory_outcomes
    (choose : List (Row × Outcome) → Row) (n : ℕ)
    (history : List (Row × Outcome)) (path : OnlineOutcomePath Outcome n) :
    (onlineSequentialPathHistory choose n history path).map Prod.snd =
      history.map Prod.snd ++ FinitePath.nextStates n path := by
  induction n generalizing history with
  | zero => simp [onlineSequentialPathHistory,FinitePath.nextStates]
  | succ n ih =>
    rw [onlineSequentialPathHistory,ih]
    simp [FinitePath.nextStates,List.append_assoc]

/-- Singleton dummy actions carry no additional information; the successor
list uniquely identifies a finite direct outcome path. -/
theorem onlineOutcomePath_nextStates_injective (n : ℕ) :
    Function.Injective (FinitePath.nextStates (State := Outcome) (Action := PUnit) n) := by
  induction n with
  | zero => intro p q _; cases p; cases q; rfl
  | succ n ih =>
    intro p q h
    rcases p with ⟨u,x,p⟩
    rcases q with ⟨v,y,q⟩
    have hh : x=y ∧ FinitePath.nextStates n p=FinitePath.nextStates n q := by
      simpa only [FinitePath.nextStates,List.cons.injEq] using h
    have hp := ih hh.2
    have hu : u=v := Subsingleton.elim _ _
    cases hh.1
    cases hp
    cases hu
    rfl

/-- Thus two direct sequential paths never collapse to the same full transcript. -/
theorem onlineSequentialPathHistory_injective
    (choose : List (Row × Outcome) → Row) (n : ℕ) (history : List (Row × Outcome)) :
    Function.Injective (onlineSequentialPathHistory choose n history) := by
  intro p q h
  have hm := congrArg (List.map Prod.snd) h
  rw [onlineSequentialPathHistory_outcomes,onlineSequentialPathHistory_outcomes] at hm
  exact onlineOutcomePath_nextStates_injective n (List.append_cancel_left hm)

theorem onlineTranscriptRowSequence_agrees (fallback : Row) (history : List (Row × Outcome))
    (j : Fin history.length) :
    onlineTranscriptRowSequence fallback history j.val=(history.get j).1 := by
  simp [onlineTranscriptRowSequence,j.isLt]

end StatisticalRL.OnlineRL
