import Formalization.Online.Regret.T3.OnlineRegretT3PathFactorization
import Formalization.Online.Regret.T3.OnlineRegretT3Centering

/-!
# Zero residual integral along actual continuation fibers

finite-sum bridge. For each fixed realized prefix, the actual
recursive path law factors into its prefix atom and conditional continuation
law. The next T₃ residual then integrates to zero under that continuation law.
This module does not yet identify every fiber of the joint reset-vector
filtration or state a conditional-expectation theorem.
-/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]

/-- For a fixed prefix, summing the actual full-law mass over all continuation
paths, weighted by a residual of the first new outcome, gives the prefix mass
multiplied by the selected-row expectation. This is an exact finite sum and
uses no division by the prefix mass. -/
theorem onlineSequentialOutcomeLaw_continuation_first_sum
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row)
    (n m : ℕ) (history : List (Row × Outcome))
    (prePath : OnlineOutcomePath Outcome n) (f : Outcome → ℝ) :
    (∑ suffix : OnlineOutcomePath Outcome (m + 1),
      (onlineSequentialOutcomeLaw d choose ((m + 1) + n) history).prob
        (onlineSequentialPathAppend n (m + 1) prePath suffix) * f suffix.2.1) =
      (onlineSequentialOutcomeLaw d choose n history).prob prePath *
        (d (choose (onlineSequentialPathHistory choose n history prePath))).expectation f := by
  classical
  let prefixMass := (onlineSequentialOutcomeLaw d choose n history).prob prePath
  let continuation := onlineSequentialOutcomeLaw d choose (m + 1)
    (onlineSequentialPathHistory choose n history prePath)
  calc
    (∑ suffix : OnlineOutcomePath Outcome (m + 1),
        (onlineSequentialOutcomeLaw d choose ((m + 1) + n) history).prob
          (onlineSequentialPathAppend n (m + 1) prePath suffix) * f suffix.2.1) =
        prefixMass * ∑ suffix : OnlineOutcomePath Outcome (m + 1),
          continuation.prob suffix * f suffix.2.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro suffix hsuffix
      rw [onlineSequentialOutcomeLaw_prob_append]
      ring
    _ = prefixMass *
        (d (choose (onlineSequentialPathHistory choose n history prePath))).expectation f := by
      dsimp [continuation]
      have hfirst := onlineSequentialOutcomeLaw_firstSuccessor_expectation
        d choose m (onlineSequentialPathHistory choose n history prePath) f
      simpa only [FiniteDistribution.expectation] using congrArg
        (fun z : ℝ => prefixMass * z) hfirst

/-- The actual one-step T₃ residual has zero integral on every fixed-prefix
continuation fiber. This is the finite-sum form needed for the later joint
reset-vector/history conditional-expectation bridge. -/
theorem onlineSequentialOutcomeLaw_continuation_t3_residual_sum_zero
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row)
    (n m : ℕ) (history : List (Row × Outcome))
    (prePath : OnlineOutcomePath Outcome n) (tail : Outcome → ℝ) :
    (∑ suffix : OnlineOutcomePath Outcome (m + 1),
      (onlineSequentialOutcomeLaw d choose ((m + 1) + n) history).prob
        (onlineSequentialPathAppend n (m + 1) prePath suffix) *
        ((d (choose (onlineSequentialPathHistory choose n history prePath))).expectation tail -
          tail suffix.2.1)) = 0 := by
  classical
  let f : Outcome → ℝ := fun x =>
    (d (choose (onlineSequentialPathHistory choose n history prePath))).expectation tail -
      tail x
  change (∑ suffix : OnlineOutcomePath Outcome (m + 1),
      (onlineSequentialOutcomeLaw d choose ((m + 1) + n) history).prob
        (onlineSequentialPathAppend n (m + 1) prePath suffix) * f suffix.2.1) = 0
  rw [onlineSequentialOutcomeLaw_continuation_first_sum]
  have hrow :
      (d (choose (onlineSequentialPathHistory choose n history prePath))).expectation
        f = 0 := by
    rw [FiniteDistribution.expectation_sub,
      FiniteDistribution.expectation_const]
    ring
  rw [hrow]
  ring

/-- The same zero continuation sum under the actual joint reset/path law, with
the reset vector fixed. The reset factor is the true source-law atom; it is
not assumed positive and no conditional probability is formed. -/
theorem onlineSequentialEpisodeLaw_sourceT3_fiber_sum_zero
    {State Action : Type*} [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ)
    (prePath : OnlineOutcomePath State (k.val * H + h.val)) :
    let n := k.val * H + h.val
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let rowLaw := onlineMDPSuccessorRowLaw E
    let history := onlineSequentialPathHistory choose n [] prePath
    let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
    (∑ suffix : OnlineOutcomePath State (m + 1),
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob
        (initial, onlineSequentialPathAppend n (m + 1) prePath suffix) *
        ((rowLaw (choose history)).expectation tail - tail suffix.2.1)) = 0 := by
  classical
  dsimp
  let n := k.val * H + h.val
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let history := onlineSequentialPathHistory choose n [] prePath
  let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
  let f : State → ℝ := fun x => (rowLaw (choose history)).expectation tail - tail x
  have hrow : (rowLaw (choose history)).expectation f = 0 := by
    dsimp [f]
    rw [FiniteDistribution.expectation_sub,
      FiniteDistribution.expectation_const]
    ring
  have hsum := onlineSequentialOutcomeLaw_continuation_first_sum
    rowLaw choose n m [] prePath f
  change (∑ suffix : OnlineOutcomePath State (m + 1),
      ((onlineInitialVectorLaw ρ K).prob initial *
        (onlineSequentialOutcomeLaw rowLaw choose ((m + 1) + n) []).prob
          (onlineSequentialPathAppend n (m + 1) prePath suffix)) *
        f suffix.2.1) = 0
  calc
    _ = (onlineInitialVectorLaw ρ K).prob initial *
        ∑ suffix : OnlineOutcomePath State (m + 1),
          (onlineSequentialOutcomeLaw rowLaw choose ((m + 1) + n) []).prob
            (onlineSequentialPathAppend n (m + 1) prePath suffix) * f suffix.2.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro suffix hsuffix
      ring
    _ = (onlineInitialVectorLaw ρ K).prob initial *
        ((onlineSequentialOutcomeLaw rowLaw choose n []).prob prePath *
          (rowLaw (choose history)).expectation f) := by
      rw [hsum]
    _ = 0 := by rw [hrow]; ring

end StatisticalRL.OnlineRL
