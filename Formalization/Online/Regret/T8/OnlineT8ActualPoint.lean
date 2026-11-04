import Formalization.Online.Regret.T8.OnlineT8ActualVariance
import Formalization.Online.Regret.T5.OnlineT5Decomposition
import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! Actual-law variance and gap proof component: OnlineT8ActualPoint.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8PointState : DecidableEq State := Classical.decEq State
noncomputable local instance t8PointAction : DecidableEq Action := Classical.decEq Action

 theorem onlineT8PaddedY_eq_actual_point
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    onlineT8PaddedY H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂ (k.val * H + h.val) (initial, path) =
      ((E h).transition sa.1 sa.2).expectation (fun s => (U s)^2) -
        (U (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 := by
  classical
  dsimp only
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let n := k.val * H + h.val
  have hn : n < K * H := by
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hlen : history.length = K * H := by
    simpa [history] using onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let record := history.get ⟨n, by rw [hlen]; exact hn⟩
  let observed := onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) (initial, path)
  have hpref : (history.take n).length = n := by simp [List.length_take, hlen, Nat.min_eq_left hn.le]
  have hcut : k.val * H ≤ n := by dsimp [n]; omega
  have hdiv : n / H = k.val := by
    dsimp [n]
    rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val, Nat.add_mul_div_left]
    · simp [Nat.div_eq_of_lt h.isLt]
    · exact hH
  have hmod : n % H = h.val := by
    dsimp [n]
    rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  have hobs : observed.2 = history.take n ++ [(record.1, record.2)] := by
    have ho : observed.2 = history.take (n + 1) := by
      simp [observed, onlineT3CommonPrefixObservation, onlineT3CommonFullHistory, history]
    rw [ho]
    simpa only [record, Prod.mk.eta] using (List.take_concat_get' history n (by rw [hlen]; exact hn)).symm
  have hres := onlinePredictableTestFromObservedPrefix_append H K E n
    (onlineT8PredictableSquare H K hH E (Real.log (1 / δ)) c₁ c₂ n)
    (history.take n) record.1 record.2 observed hpref hobs
  have hpadded : onlineT8PaddedY H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂ n (initial, path) =
      (onlineMDPSuccessorRowLaw E record.1).expectation
        (onlineT8PredictableSquare H K hH E (Real.log (1 / δ)) c₁ c₂ n initial (history.take n)) -
      onlineT8PredictableSquare H K hH E (Real.log (1 / δ)) c₁ c₂ n initial (history.take n) record.2 := by
    simpa [onlineT8PaddedY, hn, onlinePredictableObservedY, observed] using hres
  have hrecord : record.1.2 = onlineActualStageRowSequence H K hH initial fallback planner path h k.val := by
    simp [onlineActualStageRowSequence, onlineTranscriptRowSequence, record, history, n, hn, hlen]
  have htag : record.1.1 = h := by
    have hr := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
    exact congrArg Prod.fst (by simpa [record, n, history] using hr)
  have hsucc : record.2 = onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k := by
    rfl
  have htail : onlineT8PredictableSquare H K hH E (Real.log (1 / δ)) c₁ c₂ n initial (history.take n) =
      fun s => (onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2 := by
    funext s
    simp [onlineT8PredictableSquare, onlineT3CompletedPrefixTail, onlineActualOptimisticContinuation,
      onlineCappedBackwardValueAt, onlinePreEpisodePlanningStages, hdiv, hmod, List.take_take,
      Nat.min_eq_left hcut, planner, history]
  rw [hpadded, htail, hsucc]
  cases hr : record.1 with
  | mk h' sa =>
    have ht : h' = h := by simpa [hr] using htag
    subst h'
    simpa only [onlineMDPSuccessorRowLaw, hr, planner] using congrArg (fun x : State × Action =>
      ((E h).transition x.1 x.2).expectation (fun s => (onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2) -
      (onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2) hrecord
end StatisticalRL.OnlineRL
