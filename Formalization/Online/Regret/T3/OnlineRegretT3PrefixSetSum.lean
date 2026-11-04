import Formalization.Online.Regret.T3.OnlineRegretT3PrefixFiber

/-!
# Arbitrary-prefix-set zero sum under the actual joint law

This is the finite-sum form of the conditional-centering set-integral check.
For every target subset of reset-vector/prefix-history values, reindex the full
actual sample law into reset vector, prefix path and suffix path. The target
membership depends only on the first two coordinates; each suffix sum is the
already proved source T₃ fiber identity. No conditional-mean premise or
positive-mass division is used.
-/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance onlineT3SetStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineT3SetActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action

/-- The pointwise T₃ residual weight restricted to a set of observed prefix
values. Its noncomputable indicator keeps arbitrary target sets free of a
decidability premise. -/
noncomputable def onlineT3PrefixSetResidualWeight
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ)
    (target : Set ((Fin K → State) × List (OnlineMDPRow State Action H × State)))
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + (k.val * H + h.val))) : ℝ := by
  classical
  let n := k.val * H + h.val
  let history := onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2
  let choose := onlineEpisodicChoose H K hH sample.1 fallback planner
  let rowLaw := onlineMDPSuccessorRowLaw E
  let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
  exact if (sample.1, history) ∈ target then
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob sample *
      ((rowLaw (choose history)).expectation tail -
        tail (onlineSequentialPathSuffix n (m + 1) sample.2).2.1)
    else 0

/-- The actual joint reset/path weighted residual has zero finite sum over the
preimage of any set of `(reset vector, observed n-record history)` values.
The history map is the actual causal source selector. -/
theorem onlineSequentialEpisodeLaw_sourceT3_prefixSet_sum_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ)
    (target : Set ((Fin K → State) × List (OnlineMDPRow State Action H × State))) :
    let n := k.val * H + h.val
    (∑ sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n),
      onlineT3PrefixSetResidualWeight H K hH E ρ fallback planner k h L c₁ c₂ m
        target sample) = 0 := by
  classical
  dsimp
  let n := k.val * H + h.val
  let e : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State ((m + 1) + n)) ≃
      (Fin K → State) ×
        (OnlineOutcomePath.{uState, 0} State n × OnlineOutcomePath.{uState, 0} State (m + 1)) :=
    Equiv.prodCongr (Equiv.refl _) (onlineSequentialPathSplitEquiv n (m + 1))
  let f := onlineT3PrefixSetResidualWeight H K hH E ρ fallback planner k h L c₁ c₂ m target
  let g := fun split : (Fin K → State) ×
      (OnlineOutcomePath.{uState, 0} State n × OnlineOutcomePath.{uState, 0} State (m + 1)) =>
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH split.1 fallback planner) n [] split.2.1
    let choose := onlineEpisodicChoose H K hH split.1 fallback planner
    let rowLaw := onlineMDPSuccessorRowLaw E
    let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
    if (split.1, history) ∈ target then
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner ((m + 1) + n)).prob
          (split.1, onlineSequentialPathAppend n (m + 1) split.2.1 split.2.2) *
        ((rowLaw (choose history)).expectation tail - tail split.2.2.2.1)
    else 0
  have hsum : (∑ sample, f sample) = ∑ split, g split := by
    apply Fintype.sum_equiv e f g
    intro sample
    rcases sample with ⟨initial, path⟩
    simp [e, Equiv.prodCongr_apply, Equiv.refl_apply,
      onlineSequentialPathSplitEquiv, onlineT3PrefixHistory, n,
      onlineT3PrefixSetResidualWeight, f, g,
      onlineSequentialPathAppend_prefix_suffix]
  rw [hsum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro initial hi
  apply Finset.sum_eq_zero
  intro prePath hpre
  by_cases htarget :
      (initial, onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback planner) n [] prePath) ∈ target
  · simp only [g, htarget, ↓reduceIte]
    exact onlineSequentialEpisodeLaw_sourceT3_fiber_sum_zero
      H K hH E ρ initial fallback planner k h L c₁ c₂ m prePath
  · simp [g, htarget]

end StatisticalRL.OnlineRL
