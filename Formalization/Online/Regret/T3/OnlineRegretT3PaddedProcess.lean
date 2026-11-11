import Formalization.Online.Regret.T3.OnlineRegretT3CommonFiltration

/-!
# Actual padded T₃ process on the common full-horizon space

The process below is read from the actual reconstructed transcript. At a valid
transition it uses the row and successor recorded at that transition and the
source continuation tail computed from completed episodes only; after `K*H` it
is exactly zero. This file does not yet claim concentration or regret.
-/

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

universe uState uAction uRow
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance onlineT3PadStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance onlineT3PadStateDecidableEq : DecidableEq State :=
  Classical.decEq State
noncomputable local instance onlineT3PadActionDecidableEq : DecidableEq Action :=
  Classical.decEq Action

/-- Euclidean episode/stage decomposition at a valid source transition. -/
theorem onlineT3NaturalTime_decomposition (H : ℕ) (hH : 0 < H)
    (K n : ℕ) (hn : n < K * H) :
    n / H < K ∧ n % H < H ∧ n = (n / H) * H + n % H := by
  refine ⟨?_, Nat.mod_lt n hH, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul hH).2
    simpa [Nat.mul_comm] using hn
  · have h := Nat.mod_add_div n H
    have hm := Nat.mul_comm H (n / H)
    omega

/-- The first record contributed by a nonempty continuation is its selected
row paired with that continuation's first successor. -/
theorem onlineSequentialPathHistory_take_first_record
    {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]
    (choose : List (Row × Outcome) → Row) (m : ℕ)
    (history : List (Row × Outcome))
    (suffix : OnlineOutcomePath Outcome (m + 1)) :
    (onlineSequentialPathHistory choose (m + 1) history suffix).take
        (history.length + 1) = history ++ [(choose history, suffix.2.1)] := by
  rcases suffix with ⟨u, x, tail⟩
  cases u
  obtain ⟨records, hrecords, hlen⟩ :=
    onlineSequentialPathHistory_appendList choose m
      (history ++ [(choose history, x)]) tail
  rw [onlineSequentialPathHistory, hrecords]
  have hprefix : history.length + 1 ≤ (history ++ [(choose history, x)]).length := by
    simp
  rw [List.take_append_of_le_length hprefix]
  simp

/-- The first `n+1` records of an actual reconstructed path are its revealed
`n`-record history followed by the causal row and the first successor in the
actual suffix. -/
theorem onlineSequentialPathHistory_take_succ_eq_prefix_append
    {Row : Type uRow} {Outcome : Type uState} [Fintype Row] [Fintype Outcome]
    (choose : List (Row × Outcome) → Row) (n m : ℕ)
    (path : OnlineOutcomePath.{uState, 0} Outcome ((m + 1) + n)) :
    let prePath := onlineSequentialPathPrefix n (m + 1) path
    let suffix := onlineSequentialPathSuffix n (m + 1) path
    let pref := onlineSequentialPathHistory choose n [] prePath
    (onlineSequentialPathHistory choose ((m + 1) + n) [] path).take (n + 1) =
      pref ++ [(choose pref, suffix.2.1)] := by
  dsimp
  let prePath := onlineSequentialPathPrefix n (m + 1) path
  let suffix := onlineSequentialPathSuffix n (m + 1) path
  let pref := onlineSequentialPathHistory choose n [] prePath
  have happend : onlineSequentialPathAppend n (m + 1) prePath suffix = path :=
    onlineSequentialPathAppend_prefix_suffix n (m + 1) path
  have hhist := congrArg (onlineSequentialPathHistory choose ((m + 1) + n) []) happend
  rw [onlineSequentialPathHistory_append] at hhist
  have hlen : pref.length = n := by
    dsimp [pref, prePath]
    simpa using onlineSequentialPathHistory_length choose n []
      (onlineSequentialPathPrefix n (m + 1) path)
  calc
    (onlineSequentialPathHistory choose ((m + 1) + n) [] path).take (n + 1) =
        (onlineSequentialPathHistory choose (m + 1) pref suffix).take (n + 1) := by
          rw [← hhist]
    _ = pref ++ [(choose pref, suffix.2.1)] := by
      simpa [hlen] using onlineSequentialPathHistory_take_first_record
        choose m pref suffix

/-- On an actual path, the next observed transcript is the current causal
prefix followed by the selector's chosen row and the actual next successor. -/
theorem onlineT3CommonPrefixObservation_succ_eq
    (H K T : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (m n : ℕ)
    (hT : T = (m + 1) + n)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :
    onlineT3CommonPrefixObservation H K T hH fallback planner (n + 1) sample =
      (sample.1,
        (onlineT3CommonPrefixObservation H K T hH fallback planner n sample).2 ++
          [(onlineEpisodicChoose H K hH sample.1 fallback planner
              (onlineT3CommonPrefixObservation H K T hH fallback planner n sample).2,
            (onlineSequentialPathSuffix n (m + 1) (hT ▸ sample).2).2.1)]) := by
  subst T
  dsimp [onlineT3CommonPrefixObservation, onlineT3CommonFullHistory]
  let choose : List (OnlineMDPRow State Action H × State) →
      OnlineMDPRow State Action H := onlineEpisodicChoose H K hH sample.1 fallback planner
  have hsucc := onlineSequentialPathHistory_take_succ_eq_prefix_append
    (Row := OnlineMDPRow State Action H) (Outcome := State) choose n m sample.2
  let prePath : OnlineOutcomePath.{uState, 0} State n :=
    onlineSequentialPathPrefix n (m + 1) sample.2
  let suffix : OnlineOutcomePath.{uState, 0} State (m + 1) :=
    onlineSequentialPathSuffix n (m + 1) sample.2
  let pref := onlineSequentialPathHistory choose n [] prePath
  have hlen : pref.length = n := by
    dsimp [pref, prePath]
    simpa using onlineSequentialPathHistory_length choose n []
      (onlineSequentialPathPrefix n (m + 1) sample.2)
  have happend : onlineSequentialPathAppend n (m + 1) prePath suffix = sample.2 :=
    onlineSequentialPathAppend_prefix_suffix n (m + 1) sample.2
  have hhist := congrArg (onlineSequentialPathHistory choose ((m + 1) + n) []) happend
  rw [onlineSequentialPathHistory_append] at hhist
  have hprefix : pref =
      (onlineSequentialPathHistory choose ((m + 1) + n) [] sample.2).take n := by
    calc
      pref = (onlineSequentialPathHistory choose (m + 1) pref suffix).take pref.length :=
        (onlineSequentialPathHistory_extend_take choose (m + 1) pref suffix).symm
      _ = (onlineSequentialPathHistory choose (m + 1) pref suffix).take n := by rw [hlen]
      _ = (onlineSequentialPathHistory choose ((m + 1) + n) [] sample.2).take n := by
        rw [← hhist]
  apply Prod.ext
  · rfl
  · dsimp [onlineT3CommonPrefixObservation, onlineT3CommonFullHistory]
    rw [← hprefix, hsucc]

/-- The actual common-carrier prefix field is the same comap field as the
source's split-prefix observation at every exact finite-horizon cast. -/
theorem onlineT3CommonPrefixSigma_eq_splitPrefixSigma
    (H K T : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (m n : ℕ) (hT : T = m + n) :
    onlineT3CommonPrefixSigma H K T hH fallback planner n =
      onlineT3SplitPrefixSigma H K hH E fallback planner m n T hT := by
  have hobs : onlineT3CommonPrefixObservation H K T hH fallback planner n =
      fun sample => onlineT3PrefixObservation H K hH fallback planner m n (hT ▸ sample) := by
    funext sample
    exact onlineT3CommonPrefixObservation_eq_splitPrefix
      H K T hH fallback planner m n hT sample
  simp only [onlineT3CommonPrefixSigma, onlineT3SplitPrefixSigma]
  rw [hobs]

/-- T₃ residual determined by an observed transcript of at least `n+1`
records. The current realized row and successor are the record at index `n`;
the continuation tail itself uses only the first `floor(n/H)*H` completed
records, as in the source. -/
noncomputable def onlineT3ResidualFromObservedPrefix
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (observed : (Fin K → State) × List (OnlineMDPRow State Action H × State)) : ℝ := by
  classical
  let k := n / H
  let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
  exact match observed.2[n]? with
    | none => 0
    | some (row, successor) =>
        (onlineMDPSuccessorRowLaw E row).expectation
          (onlineT3CompletedPrefixTail E observed.2 k h L c₁ c₂) -
          onlineT3CompletedPrefixTail E observed.2 k h L c₁ c₂ successor

/-- Reading the record at the next time from a prefix ending in the actual
chosen row exposes exactly the row expectation minus the realized successor.
The completed-tail cutoff is required to lie inside the already revealed
prefix, so the appended current record cannot affect the continuation value. -/
theorem onlineT3ResidualFromObservedPrefix_eq_source
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n k : ℕ) (h : Fin H)
    (pref : List (OnlineMDPRow State Action H × State)) (successor : State)
    (hlen : pref.length = n) (hcut : k * H ≤ n)
    (hdiv : k = n / H) (hmod : h.val = n % H)
    (observed : (Fin K → State) × List (OnlineMDPRow State Action H × State))
    (hobs : observed.2 = pref ++
      [(onlineEpisodicChoose H K hH observed.1 fallback planner pref, successor)]) :
    onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n observed =
      (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH observed.1 fallback planner pref)).expectation
          (onlineT3CompletedPrefixTail E pref k h L c₁ c₂) -
        onlineT3CompletedPrefixTail E pref k h L c₁ c₂ successor := by
  classical
  have hstage : h = ⟨n % H, Nat.mod_lt n hH⟩ := Fin.ext hmod
  have hcut' : k * H ≤ pref.length := by simpa [hlen] using hcut
  have htake : observed.2.take (k * H) = pref.take (k * H) := by
    rw [hobs, List.take_append_of_le_length hcut']
  have happendTake :
      (pref ++ [(onlineEpisodicChoose H K hH observed.1 fallback planner pref, successor)]).take
          (k * H) = pref.take (k * H) := by
    rw [List.take_append_of_le_length hcut']
  subst k
  have htail : onlineT3CompletedPrefixTail E observed.2 (n / H) h L c₁ c₂ =
      onlineT3CompletedPrefixTail E pref (n / H) h L c₁ c₂ := by
    rw [onlineT3CompletedPrefixTail, onlineT3CompletedPrefixTail, hobs, hstage]
    rw [happendTake]
  have htail' : onlineT3CompletedPrefixTail E
      (pref ++ [(onlineEpisodicChoose H K hH observed.1 fallback planner pref, successor)])
      (n / H) ⟨n % H, Nat.mod_lt n hH⟩ L c₁ c₂ =
      onlineT3CompletedPrefixTail E pref (n / H)
        ⟨n % H, Nat.mod_lt n hH⟩ L c₁ c₂ := by
    unfold onlineT3CompletedPrefixTail
    rw [happendTake]
  rw [onlineT3ResidualFromObservedPrefix, hstage]
  simp [hlen, hobs, htail']

/-- The padded actual T₃ process on the one full `K*H` sample space. -/
noncomputable def onlineT3PaddedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ := by
  classical
  exact if n < K * H then onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample)
    else 0

/-- At every valid transition of the `K*H`-draw experiment, the padded process
is exactly the source T₃ residual, evaluated on the same causal prefix and the
actual next successor. The finite-horizon suffix length is derived from
`n < K*H`, not added as a sampling premise. -/
theorem onlineT3PaddedY_eq_sourceT3Residual
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (n : ℕ) (hn : n < K * H)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    let k : Fin K := ⟨n / H,
      (onlineT3NaturalTime_decomposition H hH K n hn).1⟩
    let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
    let m := K * H - n - 1
    onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample =
      onlineT3SourceResidualAtPrefix H K hH E fallback planner k h L c₁ c₂ m
        (show (Fin K → State) × OnlineOutcomePath.{uState, 0} State
            ((m + 1) + (k.val * H + h.val)) from
          (show K * H = (m + 1) + (k.val * H + h.val) from by
              have hdec := onlineT3NaturalTime_decomposition H hH K n hn
              have hbase : n = n / H * H + n % H := hdec.2.2
              dsimp [m]
              change K * H = (K * H - n - 1 + 1) + (n / H * H + n % H)
              rw [← hbase]
              omega) ▸ sample) := by
  classical
  have hdec := onlineT3NaturalTime_decomposition H hH K n hn
  let k : Fin K := ⟨n / H, hdec.1⟩
  let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
  let m := K * H - n - 1
  have hnidx : n = k.val * H + h.val := hdec.2.2
  have hkval : k.val = n / H := rfl
  have hhval : h.val = n % H := rfl
  have hT : K * H = (m + 1) + (k.val * H + h.val) := by
    dsimp [m]
    rw [hkval, hhval]
    rw [← hdec.2.2]
    omega
  let sourceSample : (Fin K → State) ×
      OnlineOutcomePath.{uState, 0} State ((m + 1) + (k.val * H + h.val)) :=
    hT ▸ sample
  let sourceObs := onlineT3PrefixObservation H K hH fallback planner (m + 1)
    (k.val * H + h.val) sourceSample
  have hsplit := onlineT3CommonPrefixObservation_eq_splitPrefix
    H K (K * H) hH fallback planner (m + 1) (k.val * H + h.val) hT sample
  have hnext := onlineT3CommonPrefixObservation_succ_eq
    H K (K * H) hH fallback planner m (k.val * H + h.val) hT sample
  have hobs :
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
        (k.val * H + h.val + 1) sample).2 = sourceObs.2 ++
          [(onlineEpisodicChoose H K hH sample.1 fallback planner sourceObs.2,
            (onlineSequentialPathSuffix (k.val * H + h.val) (m + 1)
              sourceSample.2).2.1)] := by
    have hcurrent := congrArg Prod.snd hnext
    rw [hsplit] at hcurrent
    simpa [sourceObs, sourceSample] using hcurrent
  have hobsN :
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
        (n + 1) sample).2 = sourceObs.2 ++
          [(onlineEpisodicChoose H K hH sample.1 fallback planner sourceObs.2,
            (onlineSequentialPathSuffix (k.val * H + h.val) (m + 1)
              sourceSample.2).2.1)] := by
    rw [hnidx]
    exact hobs
  have hcut : k.val * H ≤ n := by rw [hkval]; exact Nat.div_mul_le_self n H
  have hformula := onlineT3ResidualFromObservedPrefix_eq_source
    H K hH E fallback planner L c₁ c₂ n k.val h sourceObs.2
    (onlineSequentialPathSuffix (k.val * H + h.val) (m + 1) sourceSample.2).2.1
    (by
      simp [sourceObs, onlineT3PrefixObservation, onlineT3PrefixHistory,
        onlineSequentialPathHistory_length, hnidx]) hcut rfl rfl
    (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
      (n + 1) sample) hobsN
  have hpadded : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample =
      onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂
        n
        (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
          (n + 1) sample) := by
    simp [onlineT3PaddedY, hn]
  rw [hpadded, hformula]
  have hsource : onlineT3SourceResidualAtPrefix H K hH E fallback planner
      k h L c₁ c₂ m sourceSample =
      (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH sample.1 fallback planner sourceObs.2)).expectation
          (onlineT3CompletedPrefixTail E sourceObs.2 k.val h L c₁ c₂) -
        onlineT3CompletedPrefixTail E sourceObs.2 k.val h L c₁ c₂
          (onlineSequentialPathSuffix (k.val * H + h.val) (m + 1) sourceSample.2).2.1 := by
    have hinitial : sourceSample.1 = sample.1 := by
      have hi := congrArg Prod.fst hsplit
      simpa [sourceObs, onlineT3PrefixObservation, onlineT3CommonPrefixObservation] using hi.symm
    simp [onlineT3SourceResidualAtPrefix, sourceObs, sourceSample,
      onlineT3PrefixObservation, onlineT3PrefixHistory, hinitial]
  exact hsource.symm

/-- Conditional centering of each valid padded T₃ increment on the actual
common prefix filtration. This transports the exact finite source bridge; it
does not assume a martingale-difference property. -/
theorem onlineT3PaddedY_condExp_zero_valid
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (n : ℕ) (hn : n < K * H) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0 := by
  classical
  have hdec := onlineT3NaturalTime_decomposition H hH K n hn
  let k : Fin K := ⟨n / H, hdec.1⟩
  let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
  let m := K * H - n - 1
  have hnidx : n = k.val * H + h.val := hdec.2.2
  have hT : K * H = (m + 1) + (k.val * H + h.val) := by
    dsimp [m]
    rw [show k.val = n / H from rfl, show h.val = n % H from rfl]
    rw [← hdec.2.2]
    omega
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  have hsig := onlineT3CommonPrefixSigma_eq_splitPrefixSigma
    H K (K * H) hH E fallback planner (m + 1) (k.val * H + h.val) hT
  have hsigN : onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n =
      onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1)
        (k.val * H + h.val) (K * H) hT := by
    simpa [hnidx] using hsig
  have hsource := onlineSequentialEpisodeLaw_sourceT3_condExp_zero_exactHorizon
    H K hH E ρ fallback planner k h L c₁ c₂ m (K * H) hT
  have hfun : (fun sample => onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample) =ᵐ[μ]
      (fun sample => onlineT3SourceResidualAtPrefix H K hH E fallback planner k h L c₁ c₂ m
        (hT ▸ sample)) := by
    filter_upwards [] with sample
    have hpoint := onlineT3PaddedY_eq_sourceT3Residual
      H K hH E ρ fallback planner L c₁ c₂ n hn sample
    simpa [k, h, m, hT] using hpoint
  dsimp [μ] at hsource ⊢
  rw [hsigN]
  exact (MeasureTheory.condExp_congr_ae hfun).trans hsource

/-- The zero-padded process is conditionally centered at every natural time;
after the `K*H` source draws its value is identically zero. -/
theorem onlineT3PaddedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0 := by
  classical
  by_cases hn : n < K * H
  · exact onlineT3PaddedY_condExp_zero_valid H K hH E ρ fallback planner
      L c₁ c₂ n hn
  · have hy : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n =
        (0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ) := by
      funext sample
      simp [onlineT3PaddedY, hn]
    rw [hy]
    simp

/-- Every padded process value is measurable at the next actual prefix
sigma-field: it is explicitly a function of that observed prefix. -/
theorem onlineT3PaddedY_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n + 1)]
      (onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n) := by
  classical
  by_cases hn : n < K * H
  · have hobs : @Measurable
        ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))
        ((Fin K → State) × List (OnlineMDPRow State Action H × State))
        (onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n + 1))
        ⊤ (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1)) := by
      intro s hs
      exact (MeasurableSpace.measurableSet_comap).2 ⟨s, hs, rfl⟩
    have hres : @Measurable
        ((Fin K → State) × List (OnlineMDPRow State Action H × State))
        ℝ ⊤ (inferInstance : MeasurableSpace ℝ)
        (onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n) := by
      intro s hs
      exact MeasurableSpace.measurableSet_top
    have hy : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n =
        fun sample => onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n
          (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
            (n + 1) sample) := by
      funext sample
      simp [onlineT3PaddedY, hn]
    rw [hy]
    exact hres.comp hobs
  · have hy : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n =
        fun _ : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) => 0 := by
      funext sample
      simp [onlineT3PaddedY, hn]
    rw [hy]
    exact measurable_const

/-- Past fields are nested along the natural padded time line. -/
theorem onlineT3PaddedFiltration_mono
    (H K : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) {n j : ℕ} (hnj : n ≤ j) :
    onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n ≤
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner j :=
  onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner hnj

end StatisticalRL.OnlineRL
