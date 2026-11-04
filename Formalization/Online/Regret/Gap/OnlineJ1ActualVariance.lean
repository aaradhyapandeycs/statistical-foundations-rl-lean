import Formalization.Online.Regret.Gap.OnlineJ1VarianceSum
import Formalization.Online.Regret.T3.OnlineRegretT3VarianceTransport

/-! Actual-law variance and gap proof component: OnlineJ1ActualVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1ActualState : MeasurableSpace State := ⊤
noncomputable local instance j1ActualStateDec : DecidableEq State := Classical.decEq State
noncomputable local instance j1ActualActionDec : DecidableEq Action := Classical.decEq Action
theorem onlineJ1PaddedRowGapSquare_eq_actualT6DifferenceTerm
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (δ c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    onlineJ1PaddedRowGapSquare H K hH E fallback (Real.log (1 / δ)) c₁ c₂
      (k.val * H + h.val) (initial, path) =
      let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      ((E h).transition sa.1 sa.2).expectation (fun s =>
        (onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k s -
          onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2) := by
  classical
  dsimp
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let n := k.val * H + h.val
  have hn : n < K * H := by
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hnH : n / H = k.val := by
    have hn' : n = h.val + H * k.val := by dsimp [n]; rw [Nat.mul_comm k.val H]; omega
    rw [hn']
    rw [Nat.add_mul_div_left]
    · simp [Nat.div_eq_of_lt h.isLt]
    · exact hH
  have hnmod : n % H = h.val := by
    have hn' : n = h.val + H * k.val := by dsimp [n]; rw [Nat.mul_comm k.val H]; omega
    rw [hn', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  have hlen : history.length = K * H := by
    simpa [history, planner] using onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hkcut : k.val * H ≤ n := by dsimp [n]; omega
  have hchoose : onlineEpisodicChoose H K hH initial fallback planner
      (history.take n) =
      (h, (onlineEpisodicCurrentState H K initial fallback (history.take n),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback (history.take n)))) := by
    simp [onlineEpisodicChoose, hlen, hn.le, hnH, hnmod,
      List.take_take, Nat.min_eq_left hkcut]
  have hrow := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
  have hrow' : (history.get ⟨n, by rw [hlen]; exact hn⟩).1 =
      (h, (onlineEpisodicCurrentState H K initial fallback (history.take n),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback (history.take n)))) := by
    simpa [history, n] using hrow
  have hrowAt := onlineTranscriptRowSequence_agrees
    (onlineEpisodicChoose H K hH initial fallback planner []) history
    ⟨n, by rw [hlen]; exact hn⟩
  have hsa : onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
      (onlineEpisodicCurrentState H K initial fallback (history.take n),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback (history.take n))) := by
    change (onlineTranscriptRowSequence
      (onlineEpisodicChoose H K hH initial fallback planner []) history n).2 = _
    rw [hrowAt, hrow']
  have htail : onlineT3CompletedPrefixTail E (history.take n) k.val h
      (Real.log (1 / δ)) c₁ c₂ =
      onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k := by
    simp [onlineT3CompletedPrefixTail, onlineActualOptimisticContinuation,
      onlineCappedBackwardValueAt, onlinePreEpisodePlanningStages, history, planner,
      List.take_take, Nat.min_eq_left hkcut]
  have hpolicyEq : onlineT4SelectedEpisodePolicy H hH planner (history.take n) k.val =
      onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂ := by
    funext t x
    simp [onlineT4SelectedEpisodePolicy, onlineCappedEpisodePolicy, planner,
      List.take_take, Nat.min_eq_left hkcut]
  have hpolicy : onlineT4PolicyTailAtPrefix H hH E planner k.val h (history.take n) =
      onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k := by
    dsimp [onlineT4PolicyTailAtPrefix, onlineActualPolicyContinuation]
    rw [hpolicyEq]
  have hnH' : (k.val * H + h.val) / H = k.val := by simpa [n] using hnH
  have hnmod' : (k.val * H + h.val) % H = h.val := by simpa [n] using hnmod
  rw [onlineJ1PaddedRowGapSquare, if_pos hn]
  simp only [hnH', hnmod']
  have hobs : onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n (initial, path) =
      (initial, history.take n) := by
    simp [onlineT3CommonPrefixObservation, onlineT3CommonFullHistory, history]
  rw [hobs]
  simp only [onlineJ1RawGap, hnH', hnmod']
  rw [hchoose, htail, hpolicy, hsa]
  simp [onlineMDPSuccessorRowLaw]

end StatisticalRL.OnlineRL
