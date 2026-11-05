import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPFixedProfileActualStage

/-! The actual deployed planner table is built at the pre-episode boundary.
This module identifies that table (and its capped-backward value family) with
the fixed-profile code selected from the same pre-episode history. -/

namespace StatisticalRL.OnlineRL

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpEpisodeStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance mvpEpisodeStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpEpisodeActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Actual stage table fixed before episode `k` begins. -/
noncomputable def onlineMVPActualPreEpisodeStages
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (k : Fin K) :
    List (OnlineObservedPlanningStage State Action) := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  exact List.ofFn (fun h : Fin H => onlineMVPActualPlanningStage E
    (onlineMVPActualStackRowAt hH initial fallback planner data)
    (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h)

/-- For each row at stage `h`, no observation from that row is added between
this episode's start and the planning time of stage `h`. -/
theorem onlineMVPActualPreEpisodeStage_eq_fixedProfile
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (k : Fin K) (h : Fin H) :
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineMVPActualPlanningStage E
      (onlineMVPActualStackRowAt hH initial fallback planner data)
      (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h =
    onlineMVPFixedProfileStage E (onlineFiniteStackExtend K fallback data)
      (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) k h := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  have hlate := onlineMVPActualPlanningStage_eq_fixedProfile hH E initial fallback
    planner data k h
  change OnlineObservedPlanningStage.mk (E h)
      (fun s a => onlineMVPSourceBatchList
        (onlineMVPRowVisitList
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data)
          (k.val * H) (h, (s, a)))) =
    OnlineObservedPlanningStage.mk (E h)
      (fun s a => onlineMVPFixedProfileBatch (onlineFiniteStackExtend K fallback data)
        (h, (s, a))
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data k (h, (s, a))))
  have hstageEq : ∀ s a,
      onlineMVPRowVisitList
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data)
          (k.val * H) (h, (s, a)) =
        onlineMVPRowVisitList
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data)
          (k.val * H + h.val) (h, (s, a)) := by
    intro s a
    rw [onlineMVPActualStackHistory_rowVisitList,
      onlineMVPActualStackHistory_rowVisitList]
    exact (onlineMVPActualRowOutcomes_preEpisode_eq hH initial fallback planner data
      k h (h, (s, a)) rfl).symm
  simp only [OnlineObservedPlanningStage.mk.injEq]
  constructor
  · trivial
  · funext s a
    rw [hstageEq s a]
    exact congrArg (fun stage => stage.observations s a) hlate

/-- The deployed pre-episode stage table is exactly the fixed-profile table
selected from its actual pre-episode history. -/
theorem onlineMVPActualPreEpisodeStages_eq_fixedProfile
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (k : Fin K) :
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineMVPActualPreEpisodeStages hH E initial fallback planner data k =
      onlineMVPFixedProfileStages E (onlineFiniteStackExtend K fallback data)
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) k := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  change List.ofFn (fun h : Fin H => onlineMVPActualPlanningStage E
      (onlineMVPActualStackRowAt hH initial fallback planner data)
      (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h) =
    List.ofFn (onlineMVPFixedProfileStage E (onlineFiniteStackExtend K fallback data)
      (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) k)
  apply congrArg List.ofFn
  funext h
  exact onlineMVPActualPreEpisodeStage_eq_fixedProfile hH E initial fallback
    planner data k h

/-- Actual and fixed-profile next-value families agree pathwise at every
stage; the family includes the deployed terminal zero. -/
theorem onlineMVPActualPreEpisodeFutureFamily_eq_fixedProfile
    {H K : ℕ} (hH : 0 < H) (cap L c₁ c₂ : ℝ)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (k : Fin K) (h : ℕ) :
    onlineMVPZeroTerminalValueFamily cap L c₁ c₂
        (fun k' => onlineMVPActualPreEpisodeStages hH E initial fallback planner data k')
        (h + 1) =
      onlineMVPFixedProfileFutureFamily cap L c₁ c₂ E (onlineFiniteStackExtend K fallback data)
        (onlineMVPActualPreEpisodeProfile hH initial fallback planner data) h := by
  classical
  have hstages := fun k' => onlineMVPActualPreEpisodeStages_eq_fixedProfile
    hH E initial fallback planner data k'
  unfold onlineMVPFixedProfileFutureFamily onlineMVPZeroTerminalFutureCode
    onlineMVPFixedProfileStages onlineMVPZeroTerminalValueFamily
  simp only [onlineMVPActualPreEpisodeStages]
  congr 1
  apply Finset.image_congr
  intro k' hk'
  exact congrArg (fun xs => onlineCappedBackwardValueAt cap L c₁ c₂ xs (h + 1))
    (hstages k')

end StatisticalRL.OnlineRL
