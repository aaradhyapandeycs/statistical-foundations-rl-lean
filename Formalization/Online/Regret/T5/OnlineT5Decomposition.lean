import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions
import Formalization.Online.Regret.T4.OnlineRegretT4ActualBridge
import Formalization.Online.Regret.Joint.W123Definitions

/-! Actual-law variance and gap proof component: OnlineT5Decomposition.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t5DecompStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t5DecompActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The actual state observed after stage h, including the terminal successor. -/
noncomputable def onlineT5ActualSuccessor
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : State :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  (history.get ⟨k.val * H + h.val, by
    have hlen := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).2

/-- Source T8: true-row squared optimistic tail minus the same realized successor. -/
noncomputable def onlineActualT8
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    ((E h).transition sa.1 sa.2).expectation (fun s => (U s)^2) -
      (U (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2

/-- The exact algebraic remainder before the within-episode index shift. -/
noncomputable def onlineT5ActualSquareRemainder
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    (U (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
      ((onlineObservedPlanningRow stage sa.1 sa.2).expectation U)^2

theorem onlineActualT5_eq_W3_add_T8_add_remainder
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) :
    onlineActualT5 H K hH E initial fallback path δ c₁ c₂ =
      (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) +
      onlineActualT8 H K hH E initial fallback path δ c₁ c₂ +
      onlineT5ActualSquareRemainder H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold onlineActualT5 onlineActualT8 onlineT5ActualSquareRemainder
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  simp only [onlineActualW3Point, FiniteDistribution.variance]
  ring
end StatisticalRL.OnlineRL
