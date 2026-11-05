import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathW3AggregateRank
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathW3T6RankSum
import Formalization.Online.Regret.MVP.MVPDecouplingDefinitions
import Formalization.Online.Regret.MVP.Decoupling.MVPDecouplingFirstInequality

/-! Projection from the stage-tagged path ranks to the state-action rows used
by the source radius. All identities below are pathwise and use the existing
exact transcript equality. -/

namespace StatisticalRL.OnlineRL

open scoped BigOperators
open StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpPathPairRankRows {H K : ℕ} (hH : 0 < H)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → ℕ → State × Action :=
  fun h k => (onlineMVPActualStackRowAt hH initial fallback planner data
    (k * H + h.val)).2

noncomputable def mvpPathPairRankValues {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) : Fin H → Fin K → State → ℝ :=
  fun h k s => onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
    (List.ofFn (fun h' : Fin H =>
      letI : Nonempty State := (E h').state_nonempty
      onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h'))
    (h.val + 1) s

noncomputable def mvpPathPairRankTransition {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) :
    Fin H → State × Action → FiniteDistribution State :=
  fun h r => (E h).transition r.1 r.2

noncomputable def mvpPathPairRankInitial {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) :
    Fin H → State × Action → FiniteDistribution State :=
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  fun _ _ => onlineUniformInitialRow

noncomputable def mvpPathPairRankFirst {H K : ℕ}
    (hK : 0 < K) (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → State × Action → FiniteDistribution State :=
  fun h r => onlineMVPActualFirstVisitRow data (h, r) hK

noncomputable def mvpPathPairRankBatch {H K : ℕ}
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin H → State × Action → Fin (Nat.log2 K) → FiniteDistribution State :=
  fun h r j => MVPUniformSource.batchRow data j h r.1 r.2

theorem onlineVisitCount_map_injective_eq {Row Tagged : Type*}
    (rows : ℕ → Row) (K : ℕ) (r : Row) (f : Row → Tagged)
    (hf : Function.Injective f) :
    onlineVisitCount (fun n => f (rows n)) K (f r) =
      onlineVisitCount rows K r := by
  classical
  unfold onlineVisitCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, heq⟩
    exact ⟨hn, hf heq⟩
  · rintro ⟨hn, heq⟩
    exact ⟨hn, congrArg f heq⟩

theorem mvp_rankErrorTotal_tagMap_eq {Stage Row Tagged State : Type*}
    [Fintype Stage] [Fintype Row] [Fintype State]
    (rows : Stage → ℕ → Row) (K : ℕ)
    (f : Stage → Row → Tagged) (hf : ∀ h, Function.Injective (f h))
    (V : Stage → Fin K → State → ℝ)
    (p initial first : Stage → Tagged → FiniteDistribution State)
    (batch : Stage → Tagged → Fin (Nat.log2 K) → FiniteDistribution State) :
    mvp_rankErrorTotal (fun h n => f h (rows h n)) K V p initial first batch =
    mvp_rankErrorTotal rows K V
      (fun h r => p h (f h r))
      (fun h r => initial h (f h r))
      (fun h r => first h (f h r))
      (fun h r j => batch h (f h r) j) := by
  classical
  unfold mvp_rankErrorTotal
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  rw [onlineVisitCount_map_injective_eq (rows h) k.val (rows h k.val)
    (f h) (hf h)]

theorem mvpVarianceT6_eq_pairRankVariance_of_transcript
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
    let rows := mvpPathPairRankRows hH initial fallback planner data
    let V := mvpPathPairRankValues hH E initial fallback planner data
      (Real.log (1 / δ)) c₁ c₂
    let p := mvpPathPairRankTransition E
    mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ =
      ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let rowsTag := mvpPathRankRows hH initial fallback planner data
  let rows := mvpPathPairRankRows hH initial fallback planner data
  let V := mvpPathPairRankValues hH E initial fallback planner data
    (Real.log (1 / δ)) c₁ c₂
  let p := mvpPathPairRankTransition E
  have hvalues (h : Fin H) (k : Fin K) :
      mvpPathStackRankValues hH E initial fallback planner data
        (Real.log (1 / δ)) c₁ c₂ h k = V h k := rfl
  have hrows (h : Fin H) (k : Fin K) :
      rowsTag h k.val = (h, rows h k.val) := by
    apply Prod.ext
    · apply Fin.ext
      have hs := onlineMVPActualStackRowAt_stage hH initial fallback planner data
        (k.val * H + h.val)
      dsimp [rowsTag, mvpPathRankRows]
      rw [hs, Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
    · rfl
  have hfull := mvpVarianceT6_eq_pathRankVarianceTotal_of_transcript
    hH hK E initial fallback data path δ c₁ c₂ htranscript
  change mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ =
    ∑ h : Fin H, ∑ k : Fin K,
      (p h (rows h k.val)).variance (V h k)
  rw [hfull]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  change (mvpPathRankTransition E h (rowsTag h k.val)).variance
      (mvpPathStackRankValues hH E initial fallback planner data
        (Real.log (1 / δ)) c₁ c₂ h k) =
    (p h (rows h k.val)).variance (V h k)
  rw [hrows h k, hvalues h k]
  rfl

theorem mvpActualW4_eq_pairRankError_of_transcript
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
    let rows := mvpPathPairRankRows hH initial fallback planner data
    let V := mvpPathPairRankValues hH E initial fallback planner data
      (Real.log (1 / δ)) c₁ c₂
    let p := mvpPathPairRankTransition E
    let q0 := mvpPathPairRankInitial hH E
    let q1 := mvpPathPairRankFirst (by omega) data
    let qb := mvpPathPairRankBatch data
    mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ =
      mvp_rankErrorTotal rows K V p q0 q1 qb := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let rowsTag := mvpPathRankRows hH initial fallback planner data
  let rows := mvpPathPairRankRows hH initial fallback planner data
  let VTag := mvpPathStackRankValues hH E initial fallback planner data
    (Real.log (1 / δ)) c₁ c₂
  let V := mvpPathPairRankValues hH E initial fallback planner data
    (Real.log (1 / δ)) c₁ c₂
  let pTag : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ r => (E r.1).transition r.2.1 r.2.2
  let q0Tag : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ _ => onlineUniformInitialRow
  let q1Tag : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ r => onlineMVPActualFirstVisitRow data r hK
  let qbTag : Fin H → OnlineMDPRow State Action H →
      Fin (Nat.log2 K) → FiniteDistribution State :=
    fun _ r j => MVPUniformSource.batchRow data j r.1 r.2.1 r.2.2
  let p := mvpPathPairRankTransition E
  let q0 := mvpPathPairRankInitial hH E
  let q1 := mvpPathPairRankFirst (by omega) data
  let qb := mvpPathPairRankBatch data
  have hrowsAll (h : Fin H) (n : ℕ) : rowsTag h n = (h, rows h n) := by
    apply Prod.ext
    · apply Fin.ext
      have hs := onlineMVPActualStackRowAt_stage hH initial fallback planner data
        (n * H + h.val)
      dsimp [rowsTag, mvpPathRankRows]
      rw [hs, Nat.mul_comm n H, Nat.add_comm (H * n) h.val,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
    · rfl
  have hrowsFn (h : Fin H) : rowsTag h = fun n => (h, rows h n) :=
    funext (hrowsAll h)
  have hrows (h : Fin H) (k : Fin K) : rowsTag h k.val = (h, rows h k.val) := by
    simpa using hrowsAll h k.val
  have hvalues (h : Fin H) (k : Fin K) : VTag h k = V h k := rfl
  have hfull := mvpVarianceW4_eq_rankErrorTotal_of_transcript
    hH hK E initial fallback data path δ c₁ c₂ htranscript
  change mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ =
    mvp_rankErrorTotal rows K V p q0 q1 qb
  have hfull' :
      mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ =
        mvp_rankErrorTotal rowsTag K VTag pTag q0Tag q1Tag qbTag := by
    change mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ =
      mvp_rankErrorTotal rowsTag K VTag pTag q0Tag q1Tag qbTag at hfull
    exact hfull
  have hreplaceRows :
      mvp_rankErrorTotal rowsTag K VTag pTag q0Tag q1Tag qbTag =
        mvp_rankErrorTotal (fun h n => (h, rows h n)) K VTag pTag q0Tag q1Tag qbTag := by
    unfold mvp_rankErrorTotal
    apply Finset.sum_congr rfl
    intro h _
    rw [hrowsFn h]
  have htransport := mvp_rankErrorTotal_tagMap_eq rows K
    (fun h r => (h, r)) (by
      intro h a b hab
      exact congrArg Prod.snd hab) VTag pTag q0Tag q1Tag qbTag
  have htransport' :
      mvp_rankErrorTotal (fun h n => (h, rows h n)) K VTag pTag q0Tag q1Tag qbTag =
        mvp_rankErrorTotal rows K VTag
          (fun h r => pTag h (h, r))
          (fun h r => q0Tag h (h, r))
          (fun h r => q1Tag h (h, r))
          (fun h r j => qbTag h (h, r) j) := htransport
  rw [hfull', hreplaceRows, htransport']
  unfold mvp_rankErrorTotal
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  rw [hvalues h k]
  simp [pTag, p, q0Tag, q0, q1Tag, q1, qbTag, qb,
    mvpPathPairRankTransition, mvpPathPairRankInitial, mvpPathPairRankFirst,
    onlineMVPActualFirstVisitRow]
  rfl

end StatisticalRL.OnlineRL
