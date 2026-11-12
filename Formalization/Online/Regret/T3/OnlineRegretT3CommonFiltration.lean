import Formalization.Online.Regret.T3.OnlineRegretT3ConditionalExpectation
import Formalization.Online.SourceOptimism.SequentialEpisodeLaw

/-!
# Common-horizon T₃ filtration wrappers

source bridge. This file puts all prefix observations on the one
actual `K*H` path carrier, proves the induced comap sigma-fields are nested,
and exposes the fixed-index centering lemma at an exact caller-supplied horizon.
It does not prove a concentration inequality or a regret theorem.
-/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance onlineT3CommonStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance onlineT3CommonStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineT3CommonActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action

/-- Reconstructing a finite suffix appends a list of exactly its outcome
records to the already revealed history. -/
theorem onlineSequentialPathHistory_appendList
    {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]
    (choose : List (Row × Outcome) → Row) (m : ℕ)
    (history : List (Row × Outcome)) (suffix : OnlineOutcomePath Outcome m) :
    ∃ records, onlineSequentialPathHistory choose m history suffix = history ++ records ∧
      records.length = m := by
  induction m generalizing history with
  | zero => exact ⟨[], by simp [onlineSequentialPathHistory], rfl⟩
  | succ m ih =>
    rcases suffix with ⟨u, x, tail⟩
    cases u
    obtain ⟨records, hrecords, hlen⟩ := ih (history ++ [(choose history, x)]) tail
    refine ⟨(choose history, x) :: records, ?_, ?_⟩
    · simp [onlineSequentialPathHistory, hrecords, List.append_assoc]
    · simp [hlen]

/-- Extending a reconstructed path history appends records; taking the old
history length recovers the original prefix. -/
theorem onlineSequentialPathHistory_extend_take
    {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]
    (choose : List (Row × Outcome) → Row) (m : ℕ)
    (history : List (Row × Outcome)) (suffix : OnlineOutcomePath Outcome m) :
    (onlineSequentialPathHistory choose m history suffix).take history.length = history := by
  obtain ⟨records, hrecords, hlen⟩ :=
    onlineSequentialPathHistory_appendList choose m history suffix
  rw [hrecords]
  simp

/-- The observed first `n` transcript records agree with the first `n` records
of the reconstructed complete history. -/
theorem onlineSequentialPathHistory_prefix_take
    {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]
    (choose : List (Row × Outcome) → Row) (n m : ℕ)
    (path : OnlineOutcomePath Outcome (m + n)) :
    onlineSequentialPathHistory choose n [] (onlineSequentialPathPrefix n m path) =
      (onlineSequentialPathHistory choose (m + n) [] path).take n := by
  let pre := onlineSequentialPathPrefix n m path
  let suffix := onlineSequentialPathSuffix n m path
  have hpath : onlineSequentialPathAppend n m pre suffix = path :=
    onlineSequentialPathAppend_prefix_suffix n m path
  have hhist := congrArg (onlineSequentialPathHistory choose (m + n) []) hpath
  rw [onlineSequentialPathHistory_append] at hhist
  have hlen : (onlineSequentialPathHistory choose n [] pre).length = n := by
    simpa using onlineSequentialPathHistory_length choose n [] pre
  calc
    onlineSequentialPathHistory choose n [] (onlineSequentialPathPrefix n m path) =
        onlineSequentialPathHistory choose n [] pre := rfl
    _ = (onlineSequentialPathHistory choose m
          (onlineSequentialPathHistory choose n [] pre) suffix).take
            (onlineSequentialPathHistory choose n [] pre).length :=
      (onlineSequentialPathHistory_extend_take choose m
        (onlineSequentialPathHistory choose n [] pre) suffix).symm
    _ = (onlineSequentialPathHistory choose m
          (onlineSequentialPathHistory choose n [] pre) suffix).take n := by rw [hlen]
    _ = (onlineSequentialPathHistory choose (m + n) [] path).take n := by rw [hhist]

/-- Complete history reconstructed under the actual causal selector. -/
noncomputable def onlineT3CommonFullHistory
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :=
  onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) T [] sample.2

/-- Common-carrier observation containing the whole reset vector and the first
`n` records of the actual reconstructed history. -/
noncomputable def onlineT3CommonPrefixObservation
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :=
  (sample.1, (onlineT3CommonFullHistory H K T hH fallback planner sample).take n)

/-- Actual prefix sigma-field on the single full-horizon sample carrier. -/
noncomputable def onlineT3CommonPrefixSigma
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :=
  (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State))).comap
    (onlineT3CommonPrefixObservation H K T hH fallback planner n)

/-- Prefix-history observation from an arbitrary deterministic split of the
same actual path. -/
theorem onlineT3CommonPrefixObservation_eq_splitPrefix
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (m n : ℕ)
    (horizon : T = m + n)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :
    onlineT3CommonPrefixObservation H K T hH fallback planner n sample =
      onlineT3PrefixObservation H K hH fallback planner m n
        (horizon ▸ sample) := by
  cases horizon
  rcases sample with ⟨initial, path⟩
  simpa [onlineT3CommonPrefixObservation, onlineT3CommonFullHistory,
      onlineT3PrefixObservation, onlineT3PrefixHistory] using
    (onlineSequentialPathHistory_prefix_take
      (onlineEpisodicChoose H K hH initial fallback planner) n m path).symm

/-- The common-horizon prefix sigma-fields are nested. -/
theorem onlineT3CommonPrefixSigma_mono
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) {n j : ℕ} (hnj : n ≤ j) :
    onlineT3CommonPrefixSigma H K T hH fallback planner n ≤
      onlineT3CommonPrefixSigma H K T hH fallback planner j := by
  intro s hs
  obtain ⟨target, htarget, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hs
  apply (MeasurableSpace.measurableSet_comap).2
  refine ⟨(fun z : (Fin K → State) × List (OnlineMDPRow State Action H × State) =>
      (z.1, z.2.take n)) ⁻¹' target, MeasurableSpace.measurableSet_top, ?_⟩
  ext sample
  simp [onlineT3CommonPrefixSigma, onlineT3CommonPrefixObservation,
    onlineT3CommonFullHistory, List.take_take, Nat.min_eq_left hnj]

/-- The source prefix sigma-field transported to a sample carrier whose path
length is named separately from its `(m+n)` split. -/
noncomputable def onlineT3SplitPrefixSigma
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (m n T : ℕ) (horizon : T = m + n) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :=
  (⊤ : MeasurableSpace ((Fin K → State) × List (OnlineMDPRow State Action H × State))).comap
    (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T =>
      onlineT3PrefixObservation H K hH fallback planner m n (horizon ▸ sample))

/-- Exact-horizon source conditional centering on a separately named full path
carrier. The equality is only a cast between two presentations of the same
actual recursive sample law. -/
theorem onlineSequentialEpisodeLaw_sourceT3_condExp_zero_exactHorizon
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m T : ℕ)
    (horizon : T = (m + 1) + (k.val * H + h.val)) :
    let n := k.val * H + h.val
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner T).rowMeasure
    let f := fun sample => onlineT3SourceResidualAtPrefix H K hH E fallback planner k h L c₁ c₂ m
      (horizon ▸ sample)
    μ[f | onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1) n T horizon] =ᵐ[μ] 0 := by
  subst T
  simpa [onlineT3SplitPrefixSigma] using
    onlineSequentialEpisodeLaw_sourceT3_condExp_zero
      H K hH E ρ fallback planner k h L c₁ c₂ m

end StatisticalRL.OnlineRL
