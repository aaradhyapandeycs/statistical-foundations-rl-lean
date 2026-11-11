import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPFixedProfileFutureCode

/-! Pathwise adapter from actual pre-episode histories to the fixed-profile
finite-stack stages. This is deterministic and does not transport probability
laws. It follows the corrected C13 power-of-two profile and C17 zero-terminal
convention. -/

namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPProfile

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpActualStageStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance mvpActualStageStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpActualStageActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The profile assigned at the start of episode `k`, computed from the
actual pre-episode transcript row counts. -/
noncomputable def onlineMVPActualPreEpisodeProfile
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    Fin K → OnlineMDPRow State Action H → ℕ := fun k r =>
  sourceMVPProfileIndex
    (onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data (k.val * H)) r).length

/-- During the first `h` stages of episode `k`, a row whose stage is `h` has
not yet been visited; hence its count still equals its pre-episode count. -/
theorem onlineMVPActualRowOutcomes_preEpisode_eq
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (k : Fin K) (h : Fin H) (r : OnlineMDPRow State Action H)
    (hr : r.1.val = h.val) :
    onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data
        (k.val * H + h.val)) r =
    onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data
        (k.val * H)) r := by
  have hstable : ∀ m, m ≤ h.val →
      onlineRowOutcomes
          (onlineMVPActualStackHistory hH initial fallback planner data (k.val * H + m)) r =
        onlineRowOutcomes
          (onlineMVPActualStackHistory hH initial fallback planner data (k.val * H)) r := by
    intro m hm
    induction m with
    | zero => simp
    | succ i ih =>
        have hiTarget : i < h.val := by omega
        have hi : i < H := lt_trans hiTarget h.isLt
        have hiStage : (k.val * H + i) % H = i := by
          simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hi]
        have hneq : onlineMVPActualStackRowAt hH initial fallback planner data
            (k.val * H + i) ≠ r := by
          intro heq
          have hval := congrArg (fun row : OnlineMDPRow State Action H => row.1.val) heq
          change (onlineMVPActualStackRowAt hH initial fallback planner data
            (k.val * H + i)).1.val = r.1.val at hval
          rw [onlineMVPActualStackRowAt_stage, hiStage, hr] at hval
          omega
        have ih' := ih (by omega)
        rw [show k.val * H + (i + 1) = (k.val * H + i) + 1 by omega,
          onlineMVPActualStackHistory_succ, onlineRowOutcomes_append_one]
        simp [hneq, ih']
  exact hstable h.val le_rfl

/-- At each stage of an episode, the actual planning-stage observation list
is exactly the source-profile-selected slice of that row's expanded stack. -/
theorem onlineMVPActualPlanningStage_eq_fixedProfile
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (k : Fin K) (h : Fin H) :
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data)
        (k.val * H + h.val) h =
      onlineMVPFixedProfileStage E (onlineFiniteStackExtend K fallback data)
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) k h := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  change OnlineObservedPlanningStage.mk (E h)
      (fun s a => onlineMVPSourceBatchList
        (onlineMVPRowVisitList
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data)
          (k.val * H + h.val) (h, (s, a)))) =
    OnlineObservedPlanningStage.mk (E h)
      (fun s a => onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data)
        (h, (s, a))
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data k (h, (s, a))))
  simp only [OnlineObservedPlanningStage.mk.injEq]
  constructor
  · trivial
  · funext s a
    let r : OnlineMDPRow State Action H := (h, (s, a))
    have htime : k.val * H + h.val ≤ K * H := by
      apply Nat.le_of_lt
      calc
        k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
        _ = (k.val + 1) * H := by rw [Nat.add_mul]; simp
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
    have hbatch := onlineMVPActualSourceBatch_eq_stackProfile hH initial fallback
      planner data (k.val * H + h.val) htime r
    have hcount := onlineMVPActualRowOutcomes_preEpisode_eq hH initial fallback
      planner data k h r rfl
    have hrows := onlineMVPActualStackHistory_rowVisitList hH initial fallback
      planner data (k.val * H + h.val) r
    let currentRows := onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data
        (k.val * H + h.val)) r
    let startRows := onlineRowOutcomes
      (onlineMVPActualStackHistory hH initial fallback planner data
        (k.val * H)) r
    let currentProfile := sourceMVPProfileIndex currentRows.length
    let startProfile := sourceMVPProfileIndex startRows.length
    change onlineMVPSourceBatchList currentRows =
      List.ofFn (fun i : Fin (onlineMVPProfileBatchSize currentProfile) =>
        data (r, ⟨onlineMVPProfileBatchStart currentProfile + i.val, by
          exact onlineMVPActualProfileBatchIndex_lt_K hH initial fallback planner data
            (k.val * H + h.val) htime r i⟩)) at hbatch
    have hprofile : currentProfile = startProfile := by
      exact congrArg sourceMVPProfileIndex (congrArg List.length hcount)
    have hbatchStream : onlineMVPSourceBatchList currentRows =
        onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data) r currentProfile := by
      calc
        onlineMVPSourceBatchList currentRows =
            List.ofFn (fun i : Fin (onlineMVPProfileBatchSize currentProfile) =>
              data (r, ⟨onlineMVPProfileBatchStart currentProfile + i.val, by
                exact onlineMVPActualProfileBatchIndex_lt_K hH initial fallback planner data
                  (k.val * H + h.val) htime r i⟩)) := hbatch
        _ = onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data)
            r currentProfile := by
          unfold onlineMVPFixedProfileBatch
          apply congrArg List.ofFn
          funext i
          have hiK' := onlineMVPActualProfileBatchIndex_lt_K hH initial fallback planner data
            (k.val * H + h.val) htime r i
          have hiK : onlineMVPProfileBatchStart currentProfile + i.val < K := by
            simpa [currentProfile] using hiK'
          by_cases hcoord : onlineMVPProfileBatchStart currentProfile + i.val < K
          · simp [onlineFiniteStackExtend, hcoord]
          · exact False.elim (hcoord hiK)
    calc
      onlineMVPSourceBatchList
          (onlineMVPRowVisitList
            (onlineMVPActualStackRowAt hH initial fallback planner data)
            (onlineMVPActualStackNextAt hH initial fallback planner data)
            (k.val * H + h.val) r) =
        onlineMVPSourceBatchList
          (onlineRowOutcomes
            (onlineMVPActualStackHistory hH initial fallback planner data
              (k.val * H + h.val)) r) := by rw [hrows]
      _ = onlineMVPSourceBatchList currentRows := rfl
      _ = onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data)
          r currentProfile := hbatchStream
      _ = onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data)
          r (onlineMVPActualPreEpisodeProfile hH initial fallback planner data k r) := by
        simpa [startRows, onlineMVPActualPreEpisodeProfile] using
          congrArg (fun j => onlineMVPFixedProfileBatch
            (onlineFiniteStackExtend K fallback data) r j) hprofile

end StatisticalRL.OnlineRL
