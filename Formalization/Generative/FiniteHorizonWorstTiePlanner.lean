import Formalization.Generative.FiniteHorizonOptimalResidualTransfer

/-! A worst-tie backward planner, used only as an analysis device.

Given true stages `es` and empirical stages `fs`, at every stage it picks, among the
actions that are optimal for the empirical backup, one that minimizes the TRUE backup
of its own true continuation. It reads the true model, so it is not the algorithm of
`Thm:sample-compl-finite`; it is a causal planner whose statistical guarantee transfers,
by domination, to every empirically optimal deterministic policy. -/

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actions optimal for the one-step backup `F.qBackup V s`. -/
noncomputable def tieSet (F : EnvironmentStage State Action) (V : State → ℝ) (s : State) :
    Finset Action := by
  classical
  exact Finset.univ.filter (fun a ↦ ∀ b, F.qBackup V s b ≤ F.qBackup V s a)

theorem mem_tieSet_iff (F : EnvironmentStage State Action) (V : State → ℝ) (s : State)
    (a : Action) : a ∈ tieSet F V s ↔ ∀ b, F.qBackup V s b ≤ F.qBackup V s a := by
  classical
  unfold tieSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem greedyAction_mem_tieSet (F : EnvironmentStage State Action) (V : State → ℝ)
    (s : State) : F.greedyAction V s ∈ tieSet F V s := by
  rw [mem_tieSet_iff]
  intro b
  letI : Nonempty Action := F.action_nonempty
  rw [F.greedyAction_max V s]
  exact le_actionMaximum _ b

theorem tieSet_nonempty (F : EnvironmentStage State Action) (V : State → ℝ) (s : State) :
    (tieSet F V s).Nonempty :=
  ⟨_, greedyAction_mem_tieSet F V s⟩

/-- Among the empirically optimal actions, one minimizing the true backup of `W`. -/
noncomputable def worstTieAction (E F : EnvironmentStage State Action) (W V : State → ℝ)
    (s : State) : Action :=
  Classical.choose (Finset.exists_min_image (tieSet F V s) (fun a ↦ E.qBackup W s a)
    (tieSet_nonempty F V s))

theorem worstTieAction_mem (E F : EnvironmentStage State Action) (W V : State → ℝ)
    (s : State) : worstTieAction E F W V s ∈ tieSet F V s :=
  (Classical.choose_spec (Finset.exists_min_image (tieSet F V s) (fun a ↦ E.qBackup W s a)
    (tieSet_nonempty F V s))).1

theorem worstTieAction_le (E F : EnvironmentStage State Action) (W V : State → ℝ)
    (s : State) (a : Action) (ha : a ∈ tieSet F V s) :
    E.qBackup W s (worstTieAction E F W V s) ≤ E.qBackup W s a :=
  (Classical.choose_spec (Finset.exists_min_image (tieSet F V s) (fun a ↦ E.qBackup W s a)
    (tieSet_nonempty F V s))).2 a ha

/-- The worst-tie backward planner on paired true (`es`) and empirical (`fs`) stages.
`default` acts only beyond the shorter list, i.e. after the episode. -/
noncomputable def worstActions (default : Action) :
    List (EnvironmentStage State Action) → List (EnvironmentStage State Action) →
      ℕ → State → Action
  | E :: es, F :: fs, 0 => worstTieAction E F
      (DecisionStage.trajectoryValue
        (EnvironmentStage.controlled es (deterministicPolicy (worstActions default es fs))))
      (EnvironmentStage.optimalValue fs)
  | _ :: es, _ :: fs, n + 1 => worstActions default es fs n
  | _, _, _ => fun _ ↦ default

theorem worstActions_cons_succ (default : Action) (E F : EnvironmentStage State Action)
    (es fs : List (EnvironmentStage State Action)) (n : ℕ) :
    worstActions default (E :: es) (F :: fs) (n + 1) = worstActions default es fs n := rfl

theorem worstActions_cons_zero (default : Action) (E F : EnvironmentStage State Action)
    (es fs : List (EnvironmentStage State Action)) :
    worstActions default (E :: es) (F :: fs) 0 = worstTieAction E F
      (DecisionStage.trajectoryValue
        (EnvironmentStage.controlled es (deterministicPolicy (worstActions default es fs))))
      (EnvironmentStage.optimalValue fs) := rfl

/-- (W1) Suffixes of the planner are the planner of the suffixes. -/
theorem worstActions_drop (default : Action) (es fs : List (EnvironmentStage State Action))
    (h k : ℕ) (s : State) :
    worstActions default es fs (h + k) s =
      worstActions default (es.drop h) (fs.drop h) k s := by
  induction h generalizing es fs with
  | zero => simp
  | succ h ih =>
    cases es with
    | nil =>
      cases fs with
      | nil => simp [worstActions]
      | cons F fs => simp [worstActions]
    | cons E es =>
      cases fs with
      | nil => simp [worstActions]
      | cons F fs =>
        simpa only [Nat.succ_add, worstActions_cons_succ, List.drop_succ_cons] using ih es fs

/-- One deterministic step of the actual trajectory value. -/
theorem trajectoryValue_controlled_cons_det (E : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (g : ℕ → State → Action) (s : State) :
    DecisionStage.trajectoryValue (EnvironmentStage.controlled (E :: es) (deterministicPolicy g)) s =
      E.qBackup (DecisionStage.trajectoryValue
        (EnvironmentStage.controlled es (deterministicPolicy (fun k ↦ g (k + 1))))) s (g 0 s) := by
  rw [EnvironmentStage.controlled, DecisionStage.trajectoryValue_cons]
  change (EnvironmentStage.pointMass (g 0 s)).expectation (fun a ↦
    E.qBackup (DecisionStage.trajectoryValue
      (EnvironmentStage.controlled es (deterministicPolicy (fun k ↦ g (k + 1))))) s a) = _
  rw [EnvironmentStage.expectation_pointMass]

theorem optimalValue_cons_eq_of_mem_tieSet (F : EnvironmentStage State Action)
    (fs : List (EnvironmentStage State Action)) (s : State) (a : Action)
    (ha : a ∈ tieSet F (EnvironmentStage.optimalValue fs) s) :
    EnvironmentStage.optimalValue (F :: fs) s = F.qBackup (EnvironmentStage.optimalValue fs) s a := by
  letI : Nonempty Action := F.action_nonempty
  change actionMaximum (F.qBackup (EnvironmentStage.optimalValue fs) s) = _
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun b _ ↦ (mem_tieSet_iff _ _ _ _).1 ha b)
  · exact le_actionMaximum _ a

theorem mem_tieSet_of_eq_optimalValue (F : EnvironmentStage State Action)
    (fs : List (EnvironmentStage State Action)) (s : State) (a : Action)
    (ha : F.qBackup (EnvironmentStage.optimalValue fs) s a =
      EnvironmentStage.optimalValue (F :: fs) s) :
    a ∈ tieSet F (EnvironmentStage.optimalValue fs) s := by
  rw [mem_tieSet_iff]
  intro b
  letI : Nonempty Action := F.action_nonempty
  rw [ha]
  exact le_actionMaximum _ b

/-- (W2, whole episode) The planner is empirically optimal. -/
theorem worstActions_empirical_optimal (default : Action) :
    ∀ (es fs : List (EnvironmentStage State Action)), es.length = fs.length → ∀ s,
      DecisionStage.trajectoryValue
          (EnvironmentStage.controlled fs (deterministicPolicy (worstActions default es fs))) s =
        EnvironmentStage.optimalValue fs s
  | [], [], _, s => by
    simp [EnvironmentStage.controlled, EnvironmentStage.optimalValue, DecisionStage.trajectoryValue_nil]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | E :: es, F :: fs, hl, s => by
    have ih := worstActions_empirical_optimal default es fs (by simpa using hl)
    rw [trajectoryValue_controlled_cons_det]
    change F.qBackup (DecisionStage.trajectoryValue (EnvironmentStage.controlled fs
      (deterministicPolicy (worstActions default es fs)))) s
        (worstActions default (E :: es) (F :: fs) 0 s) = _
    rw [show DecisionStage.trajectoryValue (EnvironmentStage.controlled fs
      (deterministicPolicy (worstActions default es fs))) = EnvironmentStage.optimalValue fs from
        funext ih]
    rw [worstActions_cons_zero]
    exact (optimalValue_cons_eq_of_mem_tieSet F fs s _ (worstTieAction_mem _ _ _ _ s)).symm

/-- (W2) The planner is empirically optimal at every suffix and state. -/
theorem worstActions_suffixOptimal (default : Action)
    (es fs : List (EnvironmentStage State Action)) (hl : es.length = fs.length) :
    SuffixOptimal fs (deterministicPolicy (worstActions default es fs)) := by
  intro n s
  rw [EnvironmentStage.controlled_drop]
  have hf : (fun k ↦ deterministicPolicy (worstActions default es fs) (n + k)) =
      deterministicPolicy (worstActions default (es.drop n) (fs.drop n)) := by
    funext k t
    exact congrArg EnvironmentStage.pointMass (worstActions_drop default es fs n k t)
  rw [hf]
  exact worstActions_empirical_optimal default _ _ (by simp [hl]) s

/-- Suffix optimality passes to every suffix. -/
theorem suffixOptimal_drop (fs : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (hf : SuffixOptimal fs π) (h : ℕ) :
    SuffixOptimal (fs.drop h) (fun k ↦ π (h + k)) := by
  intro n s
  have hh := hf (h + n) s
  rw [EnvironmentStage.controlled_drop] at hh ⊢
  rw [List.drop_drop]
  simpa only [Nat.add_assoc] using hh

/-- (W3, whole episode) Every empirically suffix-optimal deterministic policy has true
value at least that of the worst-tie planner. -/
theorem worstActions_dominated (default : Action) :
    ∀ (es fs : List (EnvironmentStage State Action)), es.length = fs.length →
    ∀ (g : ℕ → State → Action), SuffixOptimal fs (deterministicPolicy g) → ∀ s,
      DecisionStage.trajectoryValue
          (EnvironmentStage.controlled es (deterministicPolicy (worstActions default es fs))) s ≤
        DecisionStage.trajectoryValue (EnvironmentStage.controlled es (deterministicPolicy g)) s
  | [], _, _, _, _, s => by simp [EnvironmentStage.controlled]
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | E :: es, F :: fs, hl, g, hg, s => by
    have hgt : SuffixOptimal fs (deterministicPolicy (fun k ↦ g (k + 1))) :=
      suffixOptimal_tail F fs (deterministicPolicy g) hg
    have ih := worstActions_dominated default es fs (by simpa using hl) _ hgt
    -- the tail of `g` is empirically optimal, so `g 0 s` is an empirical tie
    have hgtail : DecisionStage.trajectoryValue (EnvironmentStage.controlled fs
        (deterministicPolicy (fun k ↦ g (k + 1)))) = EnvironmentStage.optimalValue fs := by
      funext t
      simpa using hgt 0 t
    have h0 := hg 0 s
    simp only [List.drop_zero] at h0
    rw [trajectoryValue_controlled_cons_det, hgtail] at h0
    have hmem := mem_tieSet_of_eq_optimalValue F fs s (g 0 s) h0
    rw [trajectoryValue_controlled_cons_det, trajectoryValue_controlled_cons_det]
    change E.qBackup (DecisionStage.trajectoryValue (EnvironmentStage.controlled es
      (deterministicPolicy (worstActions default es fs)))) s
        (worstActions default (E :: es) (F :: fs) 0 s) ≤ _
    rw [worstActions_cons_zero]
    refine (worstTieAction_le _ _ _ _ s (g 0 s) hmem).trans ?_
    unfold EnvironmentStage.qBackup
    exact add_le_add le_rfl ((E.transition s (g 0 s)).expectation_mono ih)

/-- (W3) Domination at every suffix `h` and state. -/
theorem worstActions_dominated_suffix (default : Action)
    (es fs : List (EnvironmentStage State Action)) (hl : es.length = fs.length)
    (g : ℕ → State → Action) (hg : SuffixOptimal fs (deterministicPolicy g)) (h : ℕ) (s : State) :
    policyTrajectorySuffix es (worstActions default es fs) h s ≤ policyTrajectorySuffix es g h s := by
  unfold policyTrajectorySuffix
  rw [EnvironmentStage.controlled_drop, EnvironmentStage.controlled_drop]
  have hw : (fun k ↦ deterministicPolicy (worstActions default es fs) (h + k)) =
      deterministicPolicy (worstActions default (es.drop h) (fs.drop h)) := by
    funext k t
    exact congrArg EnvironmentStage.pointMass (worstActions_drop default es fs h k t)
  rw [hw]
  exact worstActions_dominated default _ _ (by simp [hl]) (fun k ↦ g (h + k))
    (suffixOptimal_drop fs _ hg h) s

end StatisticalRL.FiniteHorizonGenerative
