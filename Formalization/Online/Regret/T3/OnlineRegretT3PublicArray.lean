import Formalization.Online.Regret.T3.OnlineRegretT3VarianceTransport
import Formalization.Online.Regret.Telescope
import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! Pointwise bridge from actual padded T₃ increments to the public episode decomposition. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3PublicStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t3PublicStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3PublicActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Each actual padded T3 increment equals the public source T3 summand in
`onlineActualEpisodeRegretTerms` at its Euclidean episode/stage index. -/
theorem onlineT3PaddedY_eq_publicEpisodeT3Stage
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ)
    (initial : Fin K → State) (path : OnlineOutcomePath State (K * H))
    (k : Fin K) (h : Fin H) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun j => onlineHistoryPlanningStage E prehist j
    let state : ℕ → State := fun j =>
      onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + j))
    let action : ℕ → Action := fun j =>
      if hj : j < H then
        (history.get ⟨k.val * H + j, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + j < k.val * H + H := Nat.add_lt_add_left hj _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂
        (k.val * H + h.val) (initial, path) =
      onlineCappedEpisodeT3 H stage state action L c₁ c₂ h.val := by
  classical
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let n := k.val * H + h.val
  let record := history.get ⟨n, by
    have hlen := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩
  let prehist := history.take (k.val * H)
  let stage : Fin H → OnlineObservedPlanningStage State Action :=
    fun j => onlineHistoryPlanningStage E prehist j
  let state : ℕ → State := fun j =>
    onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + j))
  let action : ℕ → Action := fun j =>
    if hj : j < H then
      (history.get ⟨k.val * H + j, by
        have hlen := onlineSequentialPathHistory_length
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
        rw [hlen]
        simp only [List.length_nil, zero_add]
        calc
          k.val * H + j < k.val * H + H := Nat.add_lt_add_left hj _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
    else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
  let observed := onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1)
    (initial, path)
  have hlen : history.length = K * H := by
    simpa [history] using onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hn : n < K * H := by
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hcut : k.val * H ≤ n := by dsimp [n]; omega
  have hprefix_len : (history.take n).length = n := by
    simp [List.length_take, hlen, Nat.min_eq_left hn.le]
  have hdiv : k.val = n / H := by
    dsimp [n]
    rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
      Nat.add_mul_div_left]
    · simp [Nat.div_eq_of_lt h.isLt]
    · exact hH
  have hmod : h.val = n % H := by
    dsimp [n]
    rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  have hrow := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
  have hrowTuple : record.1 =
      (h, (state h.val, planner prehist h (state h.val))) := by
    simpa [record, history, n, state, prehist] using hrow
  have hchoose : onlineEpisodicChoose H K hH initial fallback planner (history.take n) =
      (h, (state h.val, planner prehist h (state h.val))) := by
    have hpolicyPrefix : (history.take n).take (k.val * H) = prehist := by
      rw [List.take_take, Nat.min_eq_left hcut]
    have hrem : (k.val * H + n % H) % H = n % H := by
      rw [← hmod, Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
    have hsplit : n = k.val * H + n % H := by omega
    have hstateChoose : onlineEpisodicCurrentState H K initial fallback (history.take n) =
        state (n % H) := by
      rw [hsplit, hrem]
    unfold onlineEpisodicChoose
    simp only [hprefix_len, hdiv.symm, hmod.symm]
    rw [hpolicyPrefix, hstateChoose]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact congrArg state hmod.symm
      · rw [congrArg state hmod.symm]
  have happend : history.take (n + 1) = history.take n ++ [record] := by
    simpa only [record, Prod.mk.eta] using (List.take_concat_get' history n (by rw [hlen]; exact hn)).symm
  have hobs : observed.2 = history.take n ++
      [(onlineEpisodicChoose H K hH observed.1 fallback planner (history.take n), record.2)] := by
    have hobs0 : observed.2 = history.take (n + 1) := by
      simp [observed, onlineT3CommonPrefixObservation, onlineT3CommonFullHistory, history]
    rw [hobs0, happend]
    have hchoose' : onlineEpisodicChoose H K hH observed.1 fallback planner
        (history.take n) = record.1 := by
      change onlineEpisodicChoose H K hH initial fallback planner
        (history.take n) = record.1
      exact hchoose.trans hrowTuple.symm
    exact congrArg (fun row => history.take n ++ [(row, record.2)]) hchoose'.symm
  have hres := onlineT3ResidualFromObservedPrefix_eq_source
    H K hH E fallback planner L c₁ c₂ n k.val h (history.take n) record.2
    hprefix_len hcut hdiv hmod observed hobs
  have htail : onlineT3CompletedPrefixTail E (history.take n) k.val h L c₁ c₂ =
      onlineCappedBackwardValue (H : ℝ) L c₁ c₂
        ((List.ofFn stage).drop (h.val + 1)) := by
    simp [onlineT3CompletedPrefixTail, stage, prehist, List.take_take,
      Nat.min_eq_left hcut]
  have hnext_tail :
      onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1))
        (state (h.val + 1)) =
      onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1)) record.2 := by
    by_cases hnext : h.val + 1 < H
    · have hs := onlineSequentialEpisode_successor_state H K hH initial fallback planner path k h hnext
      simpa [state, history, record, n, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1))) hs
    · have hterminal : h.val + 1 = H := by omega
      have hzero : onlineCappedBackwardValue (H : ℝ) L c₁ c₂
          ((List.ofFn stage).drop (h.val + 1)) = 0 := by
        rw [hterminal]
        have hdrop : (List.ofFn stage).drop H = [] :=
          List.drop_eq_nil_of_le (by simp)
        rw [hdrop]
        rfl
      rw [hzero]
      simp
  have hpadded : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n (initial, path) =
      (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH initial fallback planner (history.take n))).expectation
        (onlineT3CompletedPrefixTail E (history.take n) k.val h L c₁ c₂) -
      onlineT3CompletedPrefixTail E (history.take n) k.val h L c₁ c₂ record.2 := by
    calc
      onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n (initial, path) =
          onlineT3ResidualFromObservedPrefix H hH E L c₁ c₂ n observed := by
        simp [onlineT3PaddedY, hn, observed]
      _ = _ := by
        have hfirst : observed.1 = initial := rfl
        rw [hfirst] at hres
        exact hres
  rw [htail] at hpadded
  have hstate : record.1.2.1 = state h.val := congrArg (fun r : OnlineMDPRow State Action H => r.2.1) hrowTuple
  have hrowAction : record.1.2.2 = planner prehist h (state h.val) :=
    congrArg (fun r : OnlineMDPRow State Action H => r.2.2) hrowTuple
  have hact : action h.val = planner prehist h (state h.val) := by
    dsimp [action]
    rw [dif_pos h.isLt]
    simpa [record, n] using hrowAction
  have hpadded' : onlineT3PaddedY H K hH E ρ fallback planner L c₁ c₂ n (initial, path) =
      ((E h).transition (state h.val) (action h.val)).expectation
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1))) -
      onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1))
        (state (h.val + 1)) := by
    rw [hpadded, hchoose, onlineMDPSuccessorRowLaw, ← hact, ← hnext_tail]
  let tail := onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val + 1))
  simpa [onlineCappedEpisodeT3, stage, state, action, tail, h.isLt] using hpadded'

end StatisticalRL.OnlineRL
