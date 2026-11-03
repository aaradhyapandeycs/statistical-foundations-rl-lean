import Formalization.Online.SourceOptimism.SuccessorStackPrefix

/-! One chronological history cylinder step;
no product-mass formula, conditional-law or online coupling is assumed. -/
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [DecidableEq Row]

/-- For a fixed prefix history, the event of its next consistent extension
is exactly the prefix event intersected with one fixed row-stream coordinate
constraint. Its coordinate label depends on the fixed history, not the sample. -/
theorem onlineStackHistory_extension_iff
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (n : ℕ) (history : List (Row × Outcome)) (hlen : history.length=n)
    (x : Outcome) :
    onlineStackHistory choose stream (n+1)=history++[(choose history,x)] ↔
      onlineStackHistory choose stream n=history ∧
      stream (choose history) (onlineRowOutcomes history (choose history)).length=x := by
  constructor
  · intro hext
    have hprefix : onlineStackHistory choose stream n=history := by
      have htake := congrArg (List.take n) hext
      have hleft : (onlineStackHistory choose stream (n+1)).take n =
          onlineStackHistory choose stream n := by
        rw [onlineStackHistory]
        exact List.take_left' (onlineStackHistory_length choose stream n)
      have hright : (history++[(choose history,x)]).take n=history := by
        exact List.take_left' hlen
      rw [hleft,hright] at htake
      exact htake
    refine ⟨hprefix, ?_⟩
    rw [onlineStackHistory,hprefix] at hext
    have hsingle := List.append_cancel_left hext
    have hpair : (choose history,
        stream (choose history) (onlineRowOutcomes history (choose history)).length) =
        (choose history,x) := by simpa using hsingle
    exact congrArg Prod.snd hpair
  · rintro ⟨hprefix,hx⟩
    rw [onlineStackHistory,hprefix,hx]

end StatisticalRL.OnlineRL
