import Formalization.Online.SourceOptimism.CappedBackwardRecursion
import Formalization.Probability.Variance
import Formalization.Online.Regret.T3.OnlineRegretT3PaddedProcess
import Formalization.Online.Predictable.OnlinePredictableTestFunction

/-! Actual-law conditional variance and range results for the padded T₃ process. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3VarStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t3VarStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3VarActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The optimistic capped continuation used by the source T₃ residual stays
in `[0,H]` for every observed history. This is a deterministic range result;
it does not treat the continuation as a true-policy value. -/
theorem onlineT3CompletedPrefixTail_range
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) (h : Fin H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    ∀ x, 0 ≤ onlineT3CompletedPrefixTail E history k h L c₁ c₂ x ∧
      onlineT3CompletedPrefixTail E history k h L c₁ c₂ x ≤ H := by
  intro x
  exact onlineCappedBackwardValue_range (H : ℝ) L c₁ c₂ (by positivity)
    hL hc₁ hc₂
    ((List.ofFn (fun j : Fin H =>
      onlineHistoryPlanningStage E (history.take (k * H)) j)).drop (h.val + 1)) x

/-- Every actual observed-prefix T₃ residual is bounded by the episode horizon.
The row mean and the realized continuation both lie in the same capped range. -/
theorem onlineT3ResidualFromObservedPrefix_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (n : ℕ)
    (observed : (Fin K → State) × List (OnlineMDPRow State Action H × State)) :
    |onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n observed| ≤ H := by
  classical
  cases hrecord : observed.2[n]? with
  | none =>
      simp [onlineT3ResidualFromObservedPrefix, hrecord]
  | some record =>
      rcases record with ⟨row, successor⟩
      let d := onlineMDPSuccessorRowLaw E row
      let tail := onlineT3CompletedPrefixTail E observed.2 (n / H)
        ⟨n % H, Nat.mod_lt n hH⟩ L c₁ c₂
      have htail x : 0 ≤ tail x ∧ tail x ≤ H := by
        exact onlineT3CompletedPrefixTail_range H K hH E observed.2 (n / H)
          ⟨n % H, Nat.mod_lt n hH⟩ L c₁ c₂ hL hc₁ hc₂ x
      have hmean0 : 0 ≤ d.expectation tail := d.expectation_nonneg fun x => (htail x).1
      have hmeanH : d.expectation tail ≤ H := d.expectation_le_const fun x => (htail x).2
      have hres : onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n observed =
          d.expectation tail - tail successor := by
        simp [onlineT3ResidualFromObservedPrefix, hrecord, d, tail]
      rw [hres]
      apply abs_le.mpr
      constructor <;> linarith [htail successor]

/-- The padded process inherits the deterministic horizon bound at valid times
and is zero afterwards. -/
theorem onlineT3PaddedY_abs_le_H
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample| ≤ H := by
  by_cases hn : n < K * H
  · simpa [onlineT3PaddedY, hn] using
      onlineT3ResidualFromObservedPrefix_abs_le H K hH E L c₁ c₂ hL hc₁ hc₂ n
        (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
          (n + 1) sample)
  · simp [onlineT3PaddedY, hn]

/-- The squared centered fresh-outcome test associated with the actual
completed-prefix continuation tail. -/
noncomputable def onlineT3FreshCenteredSquare
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ)
    (initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (x : State) : ℝ := by
  let tail := onlineT3CompletedPrefixTail E history k.val h L c₁ c₂
  let row := onlineEpisodicChoose H K hH initial fallback planner history
  let d := onlineMDPSuccessorRowLaw E row
  exact (tail x - d.expectation tail) ^ 2

/-- On the actual sequential law, the conditional second moment of the
source T₃ residual is the variance of the same selected true transition row.
All means and the continuation are functions of the observed causal prefix. -/
theorem onlineSequentialEpisodeLaw_sourceT3_conditionalVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner
      ((m + 1) + (k.val * H + h.val))).rowMeasure
    let source := onlineT3SourceResidualAtPrefix H K hH E fallback planner
      k h L c₁ c₂ m
    let obs := onlineT3PrefixObservation H K hH fallback planner
      (m + 1) (k.val * H + h.val)
    μ[(fun sample => source sample ^ 2) |
      onlineT3PrefixSigma H K hH fallback planner (m + 1) (k.val * H + h.val)] =ᵐ[μ]
      (fun sample =>
        (onlineMDPSuccessorRowLaw E
          (onlineEpisodicChoose H K hH sample.1 fallback planner (obs sample).2)).variance
          (onlineT3CompletedPrefixTail E (obs sample).2 k.val h L c₁ c₂)) := by
  classical
  dsimp
  let law := onlineSequentialEpisodeLaw H K hH E ρ fallback planner
    ((m + 1) + (k.val * H + h.val))
  let μ := law.rowMeasure
  let obs := onlineT3PrefixObservation H K hH fallback planner (m + 1)
    (k.val * H + h.val)
  let σ := onlineT3PrefixSigma H K hH fallback planner (m + 1)
    (k.val * H + h.val)
  let θ := onlineT3FreshCenteredSquare H K hH E fallback planner k h L c₁ c₂
  let source := onlineT3SourceResidualAtPrefix H K hH E fallback planner k h L c₁ c₂ m
  let f : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + (k.val * H + h.val)) → ℝ := fun sample => θ sample.1
    (onlineT3PrefixHistory H K hH fallback planner sample.1 (k.val * H + h.val)
      (m + 1) sample.2)
    (onlineSequentialPathSuffix (k.val * H + h.val) (m + 1) sample.2).2.1
  let rowVariance : (Fin K → State) × OnlineOutcomePath.{uState, 0} State
      ((m + 1) + (k.val * H + h.val)) → ℝ := fun sample =>
    (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner (obs sample).2)).variance
      (onlineT3CompletedPrefixTail E (obs sample).2 k.val h L c₁ c₂)
  have hcent := onlineSequentialEpisodeLaw_predictableTest_condExp_zero
    H K hH E ρ fallback planner (k.val * H + h.val) m
      (fun initial history x => θ initial history x)
  have hf : Integrable f μ := Integrable.of_finite
  have hg : Integrable rowVariance μ := Integrable.of_finite
  have hobs : @Measurable
      ((Fin K → State) × OnlineOutcomePath.{uState, 0} State
        ((m + 1) + (k.val * H + h.val)))
      ((Fin K → State) × List (OnlineMDPRow State Action H × State)) σ ⊤ obs := by
    intro s hs
    exact (MeasurableSpace.measurableSet_comap).2 ⟨s, hs, rfl⟩
  have hrowFunction : StronglyMeasurable[⊤]
      (fun z : (Fin K → State) × List (OnlineMDPRow State Action H × State) =>
        (onlineMDPSuccessorRowLaw E
          (onlineEpisodicChoose H K hH z.1 fallback planner z.2)).variance
          (onlineT3CompletedPrefixTail E z.2 k.val h L c₁ c₂)) :=
    StronglyMeasurable.of_discrete
  have hgmeas : StronglyMeasurable[σ] rowVariance := by
    simpa [rowVariance, obs] using hrowFunction.comp_measurable hobs
  have hle : σ ≤ ⊤ := le_top
  have hcondg : μ[rowVariance | σ] = rowVariance :=
    MeasureTheory.condExp_of_stronglyMeasurable hle hgmeas hg
  have hcenterFunction :
      (fun sample => onlinePredictableTestResidualAtPrefix H K hH E fallback planner
        (k.val * H + h.val) m (fun initial history x => θ initial history x) sample) =
        fun sample => rowVariance sample - f sample := by
    funext sample
    dsimp [onlinePredictableTestResidualAtPrefix, θ, f,
      onlineT3FreshCenteredSquare, onlineT3CompletedPrefixTail, rowVariance,
      obs, onlineT3PrefixObservation]
    rw [← (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner
        (onlineT3PrefixHistory H K hH fallback planner sample.1
          (k.val * H + h.val) (m + 1) sample.2))).variance_eq_expectation_centered_sq]
  have hcent' := hcent
  dsimp [μ, law, σ] at hcent'
  have hcent'' : μ[rowVariance - f | σ] =ᵐ[μ] 0 := by
    simpa [hcenterFunction] using hcent'
  have hsub := MeasureTheory.condExp_sub hg hf σ
  have htheta : μ[f | σ] =ᵐ[μ] rowVariance := by
    filter_upwards [hcent'', Filter.Eventually.of_forall (fun sample =>
      congrFun hcondg sample), hsub] with sample hz hgval hsubval
    have hsubpoint := hsubval
    have hdifffun : (μ[rowVariance | σ] - μ[f | σ]) sample = 0 :=
      hsubpoint.symm.trans hz
    have hdiff : μ[rowVariance | σ] sample - μ[f | σ] sample = 0 := by
      simpa using hdifffun
    have hz' : rowVariance sample - μ[f | σ] sample = 0 := by
      rw [hgval] at hdiff
      exact hdiff
    linarith
  have hsourceEq :
      (fun sample => source sample ^ 2) = f := by
    funext sample
    simp [source, onlineT3SourceResidualAtPrefix, θ, f,
      onlineT3FreshCenteredSquare, onlineT3CompletedPrefixTail]
    ring
  have hvarianceEq : rowVariance = fun sample =>
      (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH sample.1 fallback planner (obs sample).2)).variance
        (onlineT3CompletedPrefixTail E (obs sample).2 k.val h L c₁ c₂) := rfl
  simpa [source, obs, σ, μ, law, hsourceEq, rowVariance] using htheta

/-- Exact-horizon transport of the source conditional second-moment identity.
The path law is unchanged; only the name of its total length is transported. -/
theorem onlineSequentialEpisodeLaw_sourceT3_conditionalVariance_exactHorizon
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (m T : ℕ)
    (horizon : T = (m + 1) + (k.val * H + h.val)) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner T).rowMeasure
    let source := fun sample => onlineT3SourceResidualAtPrefix H K hH E fallback planner
      k h L c₁ c₂ m (horizon ▸ sample)
    let obs := fun sample => onlineT3PrefixObservation H K hH fallback planner
      (m + 1) (k.val * H + h.val) (horizon ▸ sample)
    μ[(fun sample => source sample ^ 2) |
      onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1)
        (k.val * H + h.val) T horizon] =ᵐ[μ]
      (fun sample =>
        (onlineMDPSuccessorRowLaw E
          (onlineEpisodicChoose H K hH sample.1 fallback planner (obs sample).2)).variance
          (onlineT3CompletedPrefixTail E (obs sample).2 k.val h L c₁ c₂)) := by
  subst T
  simpa [onlineT3SplitPrefixSigma] using
    onlineSequentialEpisodeLaw_sourceT3_conditionalVariance H K hH E ρ fallback planner
      k h L c₁ c₂ m

/-- The predictable true-row variance attached to the padded actual T₃ draw.
It is zero outside the finite source horizon. -/
noncomputable def onlineT3PaddedRowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ := by
  classical
  exact if hn : n < K * H then
    let dec := onlineT3NaturalTime_decomposition H hH K n hn
    let k : Fin K := ⟨n / H, dec.1⟩
    let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
    let observed := onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n sample
    (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).variance
      (onlineT3CompletedPrefixTail E observed.2 k.val h L c₁ c₂)
  else 0

/-- On the common actual `K*H`-draw law, the conditional second moment of each
valid padded T₃ increment is the variance of the actual selected true row and
the optimistic capped continuation formed from completed episodes. -/
theorem onlineT3PaddedY_sq_condExp_eq_rowVariance_valid
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (n : ℕ) (hn : n < K * H) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => (onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample) ^ 2) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (fun sample => onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample) := by
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
  have hsource := onlineSequentialEpisodeLaw_sourceT3_conditionalVariance_exactHorizon
    H K hH E ρ fallback planner k h L c₁ c₂ m (K * H) hT
  have hpointSource :
      (fun sample => onlineT3SourceResidualAtPrefix H K hH E fallback planner
        k h L c₁ c₂ m (hT ▸ sample)) =ᵐ[μ]
      (fun sample => onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample) := by
    filter_upwards [] with sample
    have hp := onlineT3PaddedY_eq_sourceT3Residual
      H K hH E ρ fallback planner L c₁ c₂ n hn sample
    simpa [k, h, m, hT] using hp.symm
  have hpointSourceSq :
      (fun sample => onlineT3SourceResidualAtPrefix H K hH E fallback planner
        k h L c₁ c₂ m (hT ▸ sample) ^ 2) =ᵐ[μ]
      (fun sample => (onlineT3PaddedY H K hH E ρ fallback planner
        L c₁ c₂ n sample) ^ 2) := by
    filter_upwards [hpointSource] with sample hp
    simpa [hp]
  have hobs :
      (fun sample => onlineT3PrefixObservation H K hH fallback planner
        (m + 1) (k.val * H + h.val) (hT ▸ sample)) =
      onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n := by
    funext sample
    have hobs' := onlineT3CommonPrefixObservation_eq_splitPrefix
      H K (K * H) hH fallback planner (m + 1) (k.val * H + h.val) hT sample
    simpa [hnidx] using hobs'.symm
  dsimp [μ] at hsource ⊢
  rw [hsigN]
  have hsource' :
      μ[(fun sample => (onlineT3PaddedY H K hH E ρ fallback planner
        L c₁ c₂ n sample) ^ 2) |
          onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1)
            (k.val * H + h.val) (K * H) hT] =ᵐ[μ]
        (fun sample =>
          (onlineMDPSuccessorRowLaw E
            (onlineEpisodicChoose H K hH sample.1 fallback planner
              (onlineT3PrefixObservation H K hH fallback planner (m + 1)
                (k.val * H + h.val) (hT ▸ sample)).2)).variance
            (onlineT3CompletedPrefixTail E
              (onlineT3PrefixObservation H K hH fallback planner (m + 1)
                (k.val * H + h.val) (hT ▸ sample)).2 k.val h L c₁ c₂)) := by
    calc
      μ[(fun sample => (onlineT3PaddedY H K hH E ρ fallback planner
          L c₁ c₂ n sample) ^ 2) |
            onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1)
              (k.val * H + h.val) (K * H) hT] =ᵐ[μ]
          μ[(fun sample => onlineT3SourceResidualAtPrefix H K hH E fallback planner
            k h L c₁ c₂ m (hT ▸ sample) ^ 2) |
              onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1)
                (k.val * H + h.val) (K * H) hT] := by
            exact MeasureTheory.condExp_congr_ae hpointSourceSq.symm
      _ =ᵐ[μ]
          (fun sample =>
            (onlineMDPSuccessorRowLaw E
              (onlineEpisodicChoose H K hH sample.1 fallback planner
                (onlineT3PrefixObservation H K hH fallback planner (m + 1)
                  (k.val * H + h.val) (hT ▸ sample)).2)).variance
              (onlineT3CompletedPrefixTail E
                (onlineT3PrefixObservation H K hH fallback planner (m + 1)
                  (k.val * H + h.val) (hT ▸ sample)).2 k.val h L c₁ c₂)) := hsource
  have hvar :
      (fun sample =>
        (onlineMDPSuccessorRowLaw E
          (onlineEpisodicChoose H K hH sample.1 fallback planner
            (onlineT3PrefixObservation H K hH fallback planner (m + 1)
              (k.val * H + h.val) (hT ▸ sample)).2)).variance
          (onlineT3CompletedPrefixTail E
            (onlineT3PrefixObservation H K hH fallback planner (m + 1)
              (k.val * H + h.val) (hT ▸ sample)).2 k.val h L c₁ c₂)) =
      (fun sample => onlineT3PaddedRowVariance H K hH E fallback planner
        L c₁ c₂ n sample) := by
    funext sample
    change (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH sample.1 fallback planner
          (onlineT3PrefixObservation H K hH fallback planner (m + 1)
            (k.val * H + h.val) (hT ▸ sample)).2)).variance
        (onlineT3CompletedPrefixTail E
          (onlineT3PrefixObservation H K hH fallback planner (m + 1)
            (k.val * H + h.val) (hT ▸ sample)).2 k.val h L c₁ c₂) =
      (if hn : n < K * H then
        let dec := onlineT3NaturalTime_decomposition H hH K n hn
        let k' : Fin K := ⟨n / H, dec.1⟩
        let h' : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
        let observed := onlineT3CommonPrefixObservation H K (K * H) hH
          fallback planner n sample
        (onlineMDPSuccessorRowLaw E
          (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).variance
          (onlineT3CompletedPrefixTail E observed.2 k'.val h' L c₁ c₂)
      else 0)
    simp only [dif_pos hn]
    have hobsSample := congrFun hobs sample
    rw [hobsSample]
  rw [hvar] at hsource'
  exact hsource'

/-- Every actual selected-row continuation variance is at most `H^2`, by the
finite-distribution variance bound and the already proved `[0,H]` range of the
optimistic continuation. -/
theorem onlineT3PaddedRowVariance_le_H_sq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    0 ≤ onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ∧
      onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ≤ (H : ℝ)^2 := by
  classical
  by_cases hn : n < K * H
  · simp only [onlineT3PaddedRowVariance, dif_pos hn]
    let dec := onlineT3NaturalTime_decomposition H hH K n hn
    let k : Fin K := ⟨n / H, dec.1⟩
    let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
    let observed := onlineT3CommonPrefixObservation H K (K * H) hH
      fallback planner n sample
    let row := onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)
    let tail := onlineT3CompletedPrefixTail E observed.2 k.val h L c₁ c₂
    have htail := onlineT3CompletedPrefixTail_range H K hH E observed.2
      k.val h L c₁ c₂ hL hc₁ hc₂
    have hsq : ∀ x, tail x ^ 2 ≤ (H : ℝ)^2 := by
      intro x
      have hx := htail x
      nlinarith
    have hexpect : row.expectation (fun x => tail x ^ 2) ≤ (H : ℝ)^2 := by
      calc
        row.expectation (fun x => tail x ^ 2) ≤ row.expectation (fun _ => (H : ℝ)^2) :=
          row.expectation_mono hsq
        _ = (H : ℝ)^2 := row.expectation_const _
    exact ⟨row.variance_nonneg tail,
      (row.variance_le_expectation_sq tail).trans hexpect⟩
  · simp [onlineT3PaddedRowVariance, hn]

/-- The padded conditional second-moment identity holds at every natural time:
valid source draws have their actual selected-row variance, and the process
and proxy are both zero after the finite experiment horizon. -/
theorem onlineT3PaddedY_sq_condExp_eq_rowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => (onlineT3PaddedY H K hH E ρ fallback planner
      L c₁ c₂ n sample) ^ 2) |
        onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (fun sample => onlineT3PaddedRowVariance H K hH E fallback planner
        L c₁ c₂ n sample) := by
  classical
  dsimp
  by_cases hn : n < K * H
  · exact onlineT3PaddedY_sq_condExp_eq_rowVariance_valid
      H K hH E ρ fallback planner L c₁ c₂ n hn
  · have hzero : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n =
        fun _ => 0 := by
      funext sample
      simp [onlineT3PaddedY, hn]
    have hzeroSq : (fun sample =>
        (onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n sample) ^ 2) = 0 := by
      funext sample
      simp [hzero]
    rw [hzeroSq]
    have hcond :
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure[
          (0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ) |
            onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =
          (0 : ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) → ℝ) :=
      MeasureTheory.condExp_zero
    rw [hcond]
    exact Filter.Eventually.of_forall (fun _ => by
      simp [onlineT3PaddedRowVariance, hn])

