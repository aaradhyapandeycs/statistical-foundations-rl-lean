import Formalization.Online.Regret.T4.OnlineRegretT4PrefixCentering

/-! actual-transcript realization of the generic predictable-test
residual. The continuation is evaluated on the n-record pref, never on the
fresh record used to evaluate its outcome. This supplies no concentration tail. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance predictableObservedStateMeasurable : MeasurableSpace State := ⊤

noncomputable def onlinePredictableTestFromObservedPrefix
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (n : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (observed : (Fin K → State) × List (OnlineMDPRow State Action H × State)) : ℝ :=
  match observed.2[n]? with
  | none => 0
  | some (row, successor) =>
    let f := θ observed.1 (observed.2.take n)
    (onlineMDPSuccessorRowLaw E row).expectation f - f successor

theorem onlinePredictableTestFromObservedPrefix_append
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (n : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (pref : List (OnlineMDPRow State Action H × State))
    (row : OnlineMDPRow State Action H) (successor : State)
    (observed : (Fin K → State) × List (OnlineMDPRow State Action H × State))
    (hlen : pref.length = n) (hobs : observed.2 = pref ++ [(row, successor)]) :
    onlinePredictableTestFromObservedPrefix H K E n θ observed =
      (onlineMDPSuccessorRowLaw E row).expectation (θ observed.1 pref) -
        θ observed.1 pref successor := by
  have htake : (pref ++ [(row, successor)]).take n = pref := by
    rw [← hlen, List.take_left]
  simp [onlinePredictableTestFromObservedPrefix, hobs, hlen, htake]

/-- The generic residual read from the actual n+1-record observation. It is
totalized by the optional record lookup outside a supplied finite horizon. -/
noncomputable def onlinePredictableObservedY
    (H K T : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (n : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T) : ℝ :=
  onlinePredictableTestFromObservedPrefix H K E n θ
    (onlineT3CommonPrefixObservation H K T hH fallback planner (n + 1) sample)

/-- The observed-record residual is exactly the selected-row residual under
the actual sequential law, at the same pref and first fresh successor. -/
theorem onlinePredictableObservedY_eq_source
    (H K T : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (n m : ℕ) (hT : T = (m + 1) + n)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State T) :
    onlinePredictableObservedY H K T hH E fallback planner n θ sample =
      onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m θ (hT ▸ sample) := by
  subst T
  let pref := (onlineT3CommonPrefixObservation H K ((m + 1) + n) hH fallback planner n sample).2
  have hobs := onlineT3CommonPrefixObservation_succ_eq
    H K ((m + 1) + n) hH fallback planner m n rfl sample
  have hlen : pref.length = n := by
    have hfull := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH sample.1 fallback planner) ((m + 1) + n) [] sample.2
    simp [pref, onlineT3CommonPrefixObservation, onlineT3CommonFullHistory, hfull,
      Nat.min_eq_left (show n ≤ (m + 1) + n by omega)]
  have hread := onlinePredictableTestFromObservedPrefix_append H K E n θ pref
    (onlineEpisodicChoose H K hH sample.1 fallback planner pref)
    (onlineSequentialPathSuffix n (m + 1) sample.2).2.1
    (onlineT3CommonPrefixObservation H K ((m + 1) + n) hH fallback planner (n + 1) sample)
    hlen (congrArg Prod.snd hobs)
  have hpref : pref = onlineT3PrefixHistory H K hH fallback planner sample.1 n (m + 1) sample.2 := by
    exact congrArg Prod.snd (onlineT3CommonPrefixObservation_eq_splitPrefix
      H K ((m + 1) + n) hH fallback planner (m + 1) n rfl sample)
  change onlinePredictableTestFromObservedPrefix H K E n θ
      (onlineT3CommonPrefixObservation H K ((m + 1) + n) hH fallback planner (n + 1) sample) = _
  rw [hread]
  simpa only [onlinePredictableTestResidualAtPrefix, onlineT3CommonPrefixObservation,
    hpref] using (rfl :
      (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH sample.1 fallback planner pref)).expectation
          (θ sample.1 pref) - θ sample.1 pref
          (onlineSequentialPathSuffix n (m + 1) sample.2).2.1 =
      (onlineMDPSuccessorRowLaw E
        (onlineEpisodicChoose H K hH sample.1 fallback planner pref)).expectation
          (θ sample.1 pref) - θ sample.1 pref
          (onlineSequentialPathSuffix n (m + 1) sample.2).2.1)

theorem onlinePredictableObservedY_condExp_zero
    (H K T : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n m : ℕ)
    (hT : T = (m + 1) + n)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner T).rowMeasure
    μ[onlinePredictableObservedY H K T hH E fallback planner n θ |
      onlineT3CommonPrefixSigma H K T hH fallback planner n] =ᵐ[μ] 0 := by
  have hfun : onlinePredictableObservedY H K T hH E fallback planner n θ =
      fun sample => onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m θ (hT ▸ sample) := by
    funext sample
    exact onlinePredictableObservedY_eq_source H K T hH E fallback planner n m hT θ sample
  rw [hfun]
  exact onlineSequentialEpisodeLaw_predictableTest_condExp_zero_common
    H K hH E ρ fallback planner n m T hT θ

theorem onlinePredictableObservedY_measurable_next
    (H K T : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (n : ℕ)
    (θ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ) :
    Measurable[onlineT3CommonPrefixSigma H K T hH fallback planner (n + 1)]
      (onlinePredictableObservedY H K T hH E fallback planner n θ) := by
  have hobs : @Measurable
      ((Fin K → State) × OnlineOutcomePath.{uState, 0} State T)
      ((Fin K → State) × List (OnlineMDPRow State Action H × State))
      (onlineT3CommonPrefixSigma H K T hH fallback planner (n + 1)) ⊤
      (onlineT3CommonPrefixObservation H K T hH fallback planner (n + 1)) := by
    intro s hs
    exact (MeasurableSpace.measurableSet_comap).2 ⟨s, hs, rfl⟩
  have hres : @Measurable
      ((Fin K → State) × List (OnlineMDPRow State Action H × State))
      ℝ ⊤ (inferInstance : MeasurableSpace ℝ)
      (onlinePredictableTestFromObservedPrefix H K E n θ) := by
    intro s hs
    exact MeasurableSpace.measurableSet_top
  exact hres.comp hobs

end StatisticalRL.OnlineRL
