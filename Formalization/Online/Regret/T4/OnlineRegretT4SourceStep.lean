import Formalization.Online.Predictable.OnlinePredictableObservedProcess

/-! actual T4 transition residual and same-policy noise bridge.
The episode-sum and episode-boundary conditional-mean steps remain separate. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t4StepStateMeasurable : MeasurableSpace State := ⊤

theorem onlineT4PolicyTailAtPrefix_take
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (planner : OnlineEpisodePlanner State Action H) (k n : ℕ) (h : Fin H)
    (history : List (OnlineMDPRow State Action H × State)) (hcut : k * H ≤ n) :
    onlineT4PolicyTailAtPrefix H hH E planner k h (history.take n) =
      onlineT4PolicyTailAtPrefix H hH E planner k h history := by
  have hpolicy : onlineT4SelectedEpisodePolicy H hH planner (history.take n) k =
      onlineT4SelectedEpisodePolicy H hH planner history k := by
    funext t s
    dsimp only [onlineT4SelectedEpisodePolicy]
    rw [List.take_take, Nat.min_eq_left hcut]
  unfold onlineT4PolicyTailAtPrefix
  rw [hpolicy]

theorem onlineT4PolicyTailAtPrefix_terminal
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (planner : OnlineEpisodePlanner State Action H) (k : ℕ) (h : Fin H)
    (history : List (OnlineMDPRow State Action H × State)) (hterminal : h.val + 1 = H) :
    onlineT4PolicyTailAtPrefix H hH E planner k h history = 0 := by
  unfold onlineT4PolicyTailAtPrefix
  rw [onlineT4SelectedStages_eq_fixed]
  have hdrop : (onlineFixedPolicyStages E (planner (history.take (k * H)))).drop
      (h.val + 1) = [] := by
    rw [hterminal]
    exact List.drop_eq_nil_of_le (by simp [onlineFixedPolicyStages])
  rw [hdrop]
  funext s
  exact DecisionStage.trajectoryValue_nil s

noncomputable def onlineT4ActualStep
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  -onlinePredictableObservedY H K (K * H) hH E fallback planner
    (k.val * H + h.val)
    (fun (_initial : Fin K → State) history =>
      onlineT4PolicyTailAtPrefix H hH E planner k.val h history) sample

/-- The same observed-record residual is the source-sign true-policy noise
on the actual sampled episode, including its zero terminal continuation. -/
theorem onlineT4ActualStep_eq_policy_noise
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (h : Fin H)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    let state := onlineT4EpisodeState H K sample.1 fallback history k.val
    let V := onlineT4PolicyTailAtPrefix H hH E planner k.val h history
    onlineT4ActualStep H K hH E fallback planner k h sample =
      V (state (h.val + 1)) -
        ((E h).transition (state h.val)
          (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h)).expectation V := by
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  let state := onlineT4EpisodeState H K sample.1 fallback history k.val
  let V := onlineT4PolicyTailAtPrefix H hH E planner k.val h history
  let n := k.val * H + h.val
  have hn : n < history.length := by
    have hlen := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    change n < (onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2).length
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  let record := history.get ⟨n, hn⟩
  let θ := fun (_initial : Fin K → State) observed =>
    onlineT4PolicyTailAtPrefix H hH E planner k.val h observed
  have hlen : (history.take n).length = n := by
    simp only [List.length_take, Nat.min_eq_left hn.le]
  have hobs : (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner
      (n + 1) sample).2 = history.take n ++ [(record.1, record.2)] := by
    simpa only [record, Prod.mk.eta] using (List.take_concat_get' history n hn).symm
  have hread := onlinePredictableTestFromObservedPrefix_append H K E n θ
    (history.take n) record.1 record.2
    (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample)
    hlen hobs
  have hstep : onlineT4ActualStep H K hH E fallback planner k h sample =
      -((onlineMDPSuccessorRowLaw E record.1).expectation V - V record.2) := by
    change -onlinePredictableTestFromObservedPrefix H K E n θ
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample) = _
    rw [hread]
    simp only [θ, V, onlineT3CommonPrefixObservation,
      onlineT4PolicyTailAtPrefix_take H hH E planner k.val n h history (Nat.le_add_right _ _)]
  have hrow := onlineSequentialEpisode_actual_row H K hH E sample.1 fallback planner sample.2 k h
  change record.1 = (h, (state h.val,
    planner (history.take (k.val * H)) h (state h.val))) at hrow
  have hlaw : onlineMDPSuccessorRowLaw E record.1 =
      (E h).transition (state h.val)
        (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h) := by
    rw [hrow, onlineT4PlayedAction_eq_selected H K hH E sample.1 fallback planner sample.2 k h]
    rfl
  have hnext : V (state (h.val + 1)) = V record.2 := by
    by_cases hh : h.val + 1 < H
    · apply congrArg V
      exact onlineSequentialEpisode_successor_state H K hH sample.1 fallback planner sample.2 k h hh
    · have ht : h.val + 1 = H := by omega
      have hv : V = 0 := onlineT4PolicyTailAtPrefix_terminal H hH E planner k.val h history ht
      simp only [hv, Pi.zero_apply]
  rw [hstep, hlaw, ← hnext]
  ring

/-- Each actual source step is centered on its actual pre-transition history. -/
theorem onlineT4ActualStep_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (k : Fin K) (h : Fin H) :
    let n := k.val * H + h.val
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT4ActualStep H K hH E fallback planner k h |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0 := by
  let n := k.val * H + h.val
  let m := K * H - n - 1
  have hn : n < K * H := by
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hT : K * H = (m + 1) + n := by dsimp [m]; omega
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let θ := fun (_initial : Fin K → State) history =>
    onlineT4PolicyTailAtPrefix H hH E planner k.val h history
  have hc := onlinePredictableObservedY_condExp_zero H K (K * H) hH E ρ fallback planner n m hT θ
  have hg := MeasureTheory.condExp_neg (μ := μ)
    (onlinePredictableObservedY H K (K * H) hH E fallback planner n θ)
    (onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n)
  exact (hg.trans hc.neg).trans (by filter_upwards [] with sample; simp)

end StatisticalRL.OnlineRL
