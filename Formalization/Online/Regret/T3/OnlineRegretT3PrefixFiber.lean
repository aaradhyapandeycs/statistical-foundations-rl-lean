import Formalization.Online.Regret.T3.OnlineRegretT3FiberIntegral
import Formalization.Online.SourceOptimism.SequentialTranscriptUniqueness

/-!
# Full joint-law T₃ prefix-fiber sum

finite-sum consumer. It identifies a fiber of the actual map
(initial reset vector, reconstructed n-record history) with all suffixes of a
fixed initial/prefix pair, then applies the already proved continuation sum.
This is still a finite set-integral precursor, not a conditional-expectation
claim.
-/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance onlineT3PrefixStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineT3PrefixActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action

/-- History visible at time `n` in a full path, using the actual episode
planner selected by that sample's reset vector. -/
noncomputable def onlineT3PrefixHistory
    (H K : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (initial : Fin K → State) (n m : ℕ)
    (path : OnlineOutcomePath.{uState, 0} State (m + n)) :
      List (OnlineMDPRow State Action H × State) :=
  @onlineSequentialPathHistory (OnlineMDPRow State Action H) State
    (onlineEpisodicChoose H K hH initial fallback planner) n []
    (show OnlineOutcomePath.{uState, 0} State n from
      @onlineSequentialPathPrefix.{uState, 0, 0} State n m path)

/-- The actual joint reset/path atom sum of the T₃ residual vanishes on every
fiber of the source prefix observation `(initial vector, first n transcript)`.
A fixed transcript has a unique direct prefix path; all remaining path atoms
are summed using the actual conditional continuation law. No division by a
prefix mass is used, including when the fiber has zero probability. -/
theorem onlineSequentialEpisodeLaw_sourceT3_prefixFiber_sum_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ)
    (prePath : OnlineOutcomePath.{uState, 0} State (k.val * H + h.val)) :
    let n := k.val * H + h.val
    let choose := onlineEpisodicChoose H K hH initial fallback planner
    let rowLaw := onlineMDPSuccessorRowLaw E
    let history := onlineSequentialPathHistory choose n [] prePath
    let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
    (∑ sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n),
      if sample.1 = initial ∧
          onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2 = history
      then
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob sample *
          ((rowLaw (choose history)).expectation tail -
            tail (onlineSequentialPathSuffix n (m + 1) sample.2).2.1)
      else 0) = 0 := by
  classical
  dsimp
  let n := k.val * H + h.val
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let history := onlineSequentialPathHistory choose n [] prePath
  let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
  let e : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n)) ≃
      (Fin K → State) ×
        (OnlineOutcomePath.{uState, 0} State n × OnlineOutcomePath.{uState, 0} State (m + 1)) :=
    Equiv.prodCongr (Equiv.refl _) (onlineSequentialPathSplitEquiv n (m + 1))
  let f := fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n) =>
    if sample.1 = initial ∧
        onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2 = history
    then
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob sample *
        ((rowLaw (choose history)).expectation tail -
          tail (onlineSequentialPathSuffix n (m + 1) sample.2).2.1)
    else 0
  let g := fun split : (Fin K → State) ×
      (OnlineOutcomePath.{uState, 0} State n × OnlineOutcomePath.{uState, 0} State (m + 1)) =>
    if split.1 = initial ∧
        onlineSequentialPathHistory choose n [] split.2.1 = history
    then
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob
          (split.1, onlineSequentialPathAppend n (m + 1) split.2.1 split.2.2) *
        ((rowLaw (choose history)).expectation tail - tail split.2.2.2.1)
    else 0
  have hprefix (p : OnlineOutcomePath.{uState, 0} State n) :
      onlineSequentialPathHistory choose n [] p = history ↔ p = prePath := by
    constructor
    · intro hh
      exact onlineSequentialPathHistory_injective choose n [] hh
    · rintro rfl
      rfl
  have hsum : (∑ sample, f sample) = ∑ split, g split := by
    apply Fintype.sum_equiv e f g
    intro sample
    rcases sample with ⟨sampleInitial, path⟩
    by_cases hi : sampleInitial = initial
    · subst sampleInitial
      simp [e, Equiv.prodCongr_apply, Equiv.refl_apply,
        onlineSequentialPathSplitEquiv, onlineT3PrefixHistory, choose, f, g,
        onlineSequentialPathAppend_prefix_suffix]
    · simp [e, Equiv.prodCongr_apply, Equiv.refl_apply,
        onlineSequentialPathSplitEquiv, choose, f, g, hi]
  rw [hsum]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single_of_mem initial (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem prePath (Finset.mem_univ _)]
    · simpa [g, hprefix, n, history, rowLaw, choose, tail] using
        onlineSequentialEpisodeLaw_sourceT3_fiber_sum_zero
          H K hH E ρ initial fallback planner k h L c₁ c₂ m prePath
    · intro p hp hne
      simp [g, hprefix, hne]
  · intro initial' hi hne
    simp [g, hprefix, hne]

end StatisticalRL.OnlineRL
