import Formalization.Online.Regret.MVP.MVPVarianceDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler

/-! Successor and T8 definitions, retained from the focused source. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The successor actually recorded at this episode and stage. -/
noncomputable def mvpVarianceSuccessor (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ)
    (h : Fin H) (k : Fin K) : State :=
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  (history.get ⟨k.val*H+h.val, by
    have hlen := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
    change k.val*H+h.val < (onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path).length
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      k.val*H+h.val < k.val*H+H := Nat.add_lt_add_left h.isLt _
      _ = (k.val+1)*H := by rw [Nat.succ_mul]
      _ ≤ K*H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).2

noncomputable def mvpVarianceT8 (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
    ((E h).transition sa.1 sa.2).expectation (fun s => (U s)^2) -
      (U (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2
end StatisticalRL.OnlineRL
