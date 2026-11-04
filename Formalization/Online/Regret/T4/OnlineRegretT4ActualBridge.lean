import Formalization.Online.Regret.T4.OnlineRegretT4Telescope

/-! same-policy/actual-path specialization of the T4 identity.
No block-return conditional expectation or Azuma bound is asserted here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineControlled_ofFn {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (π : ℕ → StationaryPolicy State Action) :
    EnvironmentStage.controlled (List.ofFn E) π =
      List.ofFn (fun h => (E h).withPolicy (π h.val)) := by
  induction H generalizing π with
  | zero => rfl
  | succ H ih =>
    rw [List.ofFn_succ, EnvironmentStage.controlled, ih, List.ofFn_succ]
    rfl

/-- One episode's policy is frozen from its completed-episode history. -/
noncomputable def onlineT4SelectedEpisodePolicy
    (H : ℕ) (hH : 0 < H) (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) :
    ℕ → StationaryPolicy State Action :=
  fun n s => EnvironmentStage.pointMass
    (planner (history.take (k * H)) ⟨n % H, Nat.mod_lt n hH⟩ s)

noncomputable def onlineT4SelectedEpisodeValue
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) (s : State) : ℝ :=
  DecisionStage.trajectoryValue
    (EnvironmentStage.controlled (List.ofFn E)
      (onlineT4SelectedEpisodePolicy H hH planner history k)) s

theorem onlineT4SelectedStages_eq_fixed
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) :
    EnvironmentStage.controlled (List.ofFn E)
        (onlineT4SelectedEpisodePolicy H hH planner history k) =
      onlineFixedPolicyStages E (planner (history.take (k * H))) := by
  rw [onlineControlled_ofFn]
  unfold onlineFixedPolicyStages
  congr 1
  funext h
  apply congrArg (E h).withPolicy
  funext s
  simp only [onlineT4SelectedEpisodePolicy, Nat.mod_eq_of_lt h.isLt]

theorem onlineT4SelectedEpisodeValue_eq_capped
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (s : State) (L c₁ c₂ : ℝ) :
    onlineT4SelectedEpisodeValue H hH E (onlineCappedGreedyPlanner E L c₁ c₂)
        history k s = onlineCappedEpisodePolicyValue H hH E history k s L c₁ c₂ := rfl

def onlineT4EpisodeState (H K : ℕ) (initial : Fin K → State) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State)) (k n : ℕ) : State :=
  onlineEpisodicCurrentState H K initial fallback (history.take (k * H + n))

/-- The action actually stored in the source sequential transcript. -/
noncomputable def onlineT4PlayedAction
    (H K : ℕ) (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H) : Action :=
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
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2

theorem onlineT4PlayedAction_eq_selected
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    onlineT4PlayedAction H K hH initial fallback planner path k h =
      planner (history.take (k.val * H)) h
        (onlineT4EpisodeState H K initial fallback history k.val h.val) := by
  have hrow := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
  simpa only [onlineT4PlayedAction, onlineT4EpisodeState] using
    congrArg (fun r : OnlineMDPRow State Action H => r.2.2) hrow

/-- Exact source-sign T4 identity for the policy and actions from the same
actual sequential episode. At the terminal step the continuation is zero. -/
theorem onlineSequentialEpisode_selectedPolicy_noise_identity
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let state := onlineT4EpisodeState H K initial fallback history k.val
    let g := planner (history.take (k.val * H))
    let D := onlineFixedPolicyStages E g
    (∑ n ∈ Finset.range H,
      if hn : n < H then (E ⟨n, hn⟩).reward (state n)
        (onlineT4PlayedAction H K hH initial fallback planner path k ⟨n, hn⟩) else 0) -
      onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k) =
    ∑ n ∈ Finset.range H,
      if hn : n < H then
        DecisionStage.trajectoryValue (D.drop (n + 1)) (state (n + 1)) -
          ((E ⟨n, hn⟩).transition (state n)
            (onlineT4PlayedAction H K hH initial fallback planner path k ⟨n, hn⟩)).expectation
            (DecisionStage.trajectoryValue (D.drop (n + 1)))
      else 0 := by
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let state := onlineT4EpisodeState H K initial fallback history k.val
  let g := planner (history.take (k.val * H))
  let D := onlineFixedPolicyStages E g
  have hprefixlen : (history.take (k.val * H)).length = k.val * H :=
    onlineSequential_episodePrefix_length H K hH E initial fallback planner path k.val k.isLt.le
  have hstate0 : state 0 = initial k := by
    simpa only [state, onlineT4EpisodeState, Nat.add_zero] using
      onlineEpisodicCurrentState_reset H K hH initial fallback
        (history.take (k.val * H)) k hprefixlen
  have hval : DecisionStage.trajectoryValue D (state 0) =
      onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k) := by
    rw [hstate0]
    unfold onlineT4SelectedEpisodeValue
    rw [onlineT4SelectedStages_eq_fixed]
  have haction : ∀ h : Fin H,
      onlineT4PlayedAction H K hH initial fallback planner path k h = g h (state h.val) := by
    intro h
    exact onlineT4PlayedAction_eq_selected H K hH E initial fallback planner path k h
  have hid := onlineFixedPolicy_return_noise_identity E g state
  dsimp only at hid
  rw [hval] at hid
  simpa only [haction] using hid

end StatisticalRL.OnlineRL
