import Formalization.Online.SourceOptimism.SequentialEpisodeLaw
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Direct sequential path atom probabilities
factor into actual chronological transition masses; no coupling premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]

noncomputable def onlineTranscriptTransitionMass
    (d : Row → FiniteDistribution Outcome) (history : List (Row × Outcome)) : ℝ :=
  (history.map (fun record => (d record.1).prob record.2)).prod

theorem onlineTranscriptTransitionMass_append_one
    (d : Row → FiniteDistribution Outcome) (history : List (Row × Outcome))
    (r : Row) (x : Outcome) :
    onlineTranscriptTransitionMass d (history++[(r,x)]) =
      onlineTranscriptTransitionMass d history*(d r).prob x := by
  simp [onlineTranscriptTransitionMass]

/-- Prefix mass times direct conditional path mass is exactly the full
reconstructed history mass. This avoids dividing by a possibly zero prefix. -/
theorem onlineSequentialOutcomeLaw_prob_mul_prefix
    (d : Row → FiniteDistribution Outcome) (choose : List (Row × Outcome) → Row)
    (n : ℕ) (history : List (Row × Outcome)) (path : OnlineOutcomePath Outcome n) :
    onlineTranscriptTransitionMass d history*
      (onlineSequentialOutcomeLaw d choose n history).prob path =
    onlineTranscriptTransitionMass d (onlineSequentialPathHistory choose n history path) := by
  induction n generalizing history with
  | zero =>
    letI : Subsingleton (OnlineOutcomePath Outcome 0) := inferInstanceAs (Subsingleton PUnit)
    have hp : (onlineSequentialOutcomeLaw d choose 0 history).prob path=1 :=
      FiniteDistribution.prob_eq_one_of_subsingleton _ _
    simp [hp,onlineSequentialPathHistory]
  | succ n ih =>
    have h := ih (history++[(choose history,path.2.1)]) path.2.2
    rw [onlineTranscriptTransitionMass_append_one] at h
    change onlineTranscriptTransitionMass d history*
      ((d (choose history)).prob path.2.1*
        (onlineSequentialOutcomeLaw d choose n
          (history++[(choose history,path.2.1)])).prob path.2.2) = _
    simpa [onlineSequentialPathHistory,mul_assoc] using h

/-- From empty history, each actual sequential path atom has its exact
transition-product density. The path's selected rows are reconstructed causally. -/
theorem onlineSequentialOutcomeLaw_prob_eq_transcriptMass
    (d : Row → FiniteDistribution Outcome) (choose : List (Row × Outcome) → Row)
    (n : ℕ) (path : OnlineOutcomePath Outcome n) :
    (onlineSequentialOutcomeLaw d choose n []).prob path =
      onlineTranscriptTransitionMass d (onlineSequentialPathHistory choose n [] path) := by
  simpa [onlineTranscriptTransitionMass] using
    onlineSequentialOutcomeLaw_prob_mul_prefix d choose n [] path

theorem onlineTranscriptTransitionMass_eq_prod
    (d : Row → FiniteDistribution Outcome) (history : List (Row × Outcome)) :
    onlineTranscriptTransitionMass d history =
      ∏ j : Fin history.length,(d (history.get j).1).prob (history.get j).2 := by
  unfold onlineTranscriptTransitionMass
  conv_lhs => rw [← List.ofFn_get history, List.map_ofFn, List.prod_ofFn]
  rfl

end StatisticalRL.OnlineRL
