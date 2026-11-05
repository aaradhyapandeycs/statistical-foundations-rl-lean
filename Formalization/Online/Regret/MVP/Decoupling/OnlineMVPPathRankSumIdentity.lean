import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathW4RankSummand
import Formalization.Online.Regret.MVP.Decoupling.MVPRankErrorDecomposition
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualTypedRankKernel

/-! Aggregate actual-path rank identities. The only path/stack input is the
exact transcript equality; no probability statement is made here. -/
namespace StatisticalRL.OnlineRL

open scoped BigOperators
open StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpPathRankRows {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → ℕ → OnlineMDPRow State Action H :=
  fun h k => onlineMVPActualStackRowAt hH initial fallback planner data (k * H + h.val)

theorem mvpVarianceW4_eq_rankErrorTotal_of_transcript
    {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ)
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
        data (K * H)) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let rows := mvpPathRankRows hH initial fallback planner data
    let V := mvpPathStackRankValues hH E initial fallback planner data
      (Real.log (1 / δ)) c₁ c₂
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    let p : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
      fun _ r => (E r.1).transition r.2.1 r.2.2
    let initialRow : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
      fun _ _ => onlineUniformInitialRow
    let first : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
      fun _ r => onlineMVPActualFirstVisitRow data r hK
    let batch : Fin H → OnlineMDPRow State Action H →
        Fin (Nat.log2 K) → FiniteDistribution State :=
      fun _ r j => MVPUniformSource.batchRow data j r.1 r.2.1 r.2.2
    mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ =
      mvp_rankErrorTotal rows K V p initialRow first batch := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let rows := mvpPathRankRows hH initial fallback planner data
  let V := mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let p : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ r => (E r.1).transition r.2.1 r.2.2
  let initialRow : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ _ => onlineUniformInitialRow
  let first : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ r => onlineMVPActualFirstVisitRow data r hK
  let batch : Fin H → OnlineMDPRow State Action H →
      Fin (Nat.log2 K) → FiniteDistribution State :=
    fun _ r j => MVPUniformSource.batchRow data j r.1 r.2.1 r.2.2
  change mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ =
    mvp_rankErrorTotal rows K V p initialRow first batch
  unfold mvpVarianceW4 mvp_rankErrorTotal
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let r := rowAt (k.val * H + h.val)
  have hsa : sa = r.2 := by
    exact mvpPathSelectedRow_eq_stackRow_of_transcript hH E initial fallback planner data
      path htranscript h k
  have htag : r.1 = h := by
    apply Fin.ext
    have hs := onlineMVPActualStackRowAt_stage hH initial fallback planner data
      (k.val * H + h.val)
    dsimp [r, rowAt]
    rw [hs]
    rw [Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  have hr : r = (h, sa) := by
    exact Prod.ext htag hsa.symm
  have hstageCount : ∀ n, n < k.val * H → (rowAt n).1.val = n % H := by
    intro n hn
    exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
  have hcount := onlineVisitCount_stage_episode_eq rowAt h k.val hH r htag hstageCount
  have hrankCount : onlineVisitCount rowAt (k.val * H) (h, sa) =
      onlineVisitCount (rows h) k.val (rows h k.val) := by
    simpa [rows, mvpPathRankRows, rowAt, r, hr] using hcount
  have hrows : rows h k.val = (h, sa) := by
    change rowAt (k.val * H + h.val) = (h, sa)
    exact hr
  have hcountPair : onlineVisitCount (rows h) k.val (h, sa) =
      onlineVisitCount rowAt (k.val * H) (h, sa) := by
    simpa [rows, mvpPathRankRows, rowAt, r, hr] using hcount.symm
  have hpoint := mvpVarianceW4_term_eq_rankError_of_transcript
    hH E initial fallback data path δ c₁ c₂ htranscript h k
  have hparam : mvp_rankPositiveError K (p h (rows h k.val)) (initialRow h (rows h k.val))
      (first h (rows h k.val)) (batch h (rows h k.val))
      (onlineVisitCount (rows h) k.val (rows h k.val)) (V h k) =
    mvp_rankPositiveError K ((E h).transition sa.1 sa.2) onlineUniformInitialRow
      (onlineMVPActualFirstVisitRow data (h, sa) hK)
      (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2)
      (onlineVisitCount rowAt (k.val * H) (h, sa)) (V h k) := by
    rw [hrows, ← hcountPair]
  have hpoint' : max ((onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPHistoryRowAt hH E fallback
          ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)))
        (onlineMVPHistoryNextAt fallback
          ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)))
        ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)).length h)
      sa.1 sa.2).expectation (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k) -
      ((E h).transition sa.1 sa.2).expectation
        (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k)) 0 =
      mvp_rankPositiveError K ((E h).transition sa.1 sa.2) onlineUniformInitialRow
        (onlineMVPActualFirstVisitRow data (h, sa) hK)
        (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2)
        (onlineVisitCount rowAt (k.val * H) (h, sa)) (V h k) := by
    simpa [sa, planner, rowAt, V, mvpPathStackRankValues] using hpoint
  exact hpoint'.trans hparam.symm

end StatisticalRL.OnlineRL
