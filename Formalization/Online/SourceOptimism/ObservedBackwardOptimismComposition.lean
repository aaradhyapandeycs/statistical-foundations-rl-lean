import Formalization.Online.SourceOptimism.ObservedHistoryPlanningAdapter

/-! Actual-history certificates feed chronological
suffix induction. This is a deterministic implication on the same transcript,
not an identification of the deployed causal planner or a probability theorem. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- One head certificate with the true chronological tail continuation. -/
def onlinePlanningHeadCertificate (cap L c₁ c₂ : ℝ)
    (stage : OnlineObservedPlanningStage State Action)
    (tail : List (OnlineObservedPlanningStage State Action)) : Prop :=
  ∀ s a, 3 ≤ (stage.observations s a).length →
    ∀ U : State → ℝ,
    (∀ x, EnvironmentStage.optimalValue (onlinePlanningEnvironments tail) x ≤ U x ∧
      U x ≤ cap) →
    (stage.environment.transition s a).expectation
        (EnvironmentStage.optimalValue (onlinePlanningEnvironments tail)) ≤
      (onlineObservedPlanningRow stage s a).expectation U +
        c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance U *
          (L / (stage.observations s a).length)) +
        c₂ * cap * (L / (stage.observations s a).length)

/-- Head certificates at all actual list suffixes assemble the recursive input
of backward induction; there is no union bound or new statistical premise. -/
theorem onlineChronologicalCertificates_of_suffixHeads
    (cap L c₁ c₂ : ℝ) (stages : List (OnlineObservedPlanningStage State Action))
    (hheads : ∀ n stage tail, stages.drop n = stage :: tail →
      onlinePlanningHeadCertificate cap L c₁ c₂ stage tail) :
    onlineChronologicalBonusCertificates cap L c₁ c₂ stages := by
  revert hheads
  induction stages with
  | nil => intro _; trivial
  | cons stage stages ih =>
    intro hheads
    constructor
    · exact hheads 0 stage stages rfl
    · apply ih
      intro n stage' tail heq
      exact hheads (n + 1) stage' tail (by simpa only [List.drop_succ_cons] using heq)

/-- A suffix retains every certificate at its actual later stages. -/
theorem onlineChronologicalCertificates_drop
    (cap L c₁ c₂ : ℝ) (stages : List (OnlineObservedPlanningStage State Action))
    (hcert : onlineChronologicalBonusCertificates cap L c₁ c₂ stages) (n : ℕ) :
    onlineChronologicalBonusCertificates cap L c₁ c₂ (stages.drop n) := by
  induction n generalizing stages with
  | zero => simpa using hcert
  | succ n ih =>
    cases stages with
    | nil => trivial
    | cons stage stages =>
      simpa only [List.drop_succ_cons] using ih stages hcert.2

/-- Exact chronological suffix: source active stage h.val+1 has the current
stage at its head and the next continuation at drop(h.val+1). -/
theorem onlinePreEpisodePlanningStages_drop_stage {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) (h : Fin H) :
    (onlinePreEpisodePlanningStages E history k).drop h.val =
      onlineHistoryPlanningStage E (history.take (k * H)) h ::
        (onlinePreEpisodePlanningStages E history k).drop (h.val + 1) := by
  have hi : h.val < (onlinePreEpisodePlanningStages E history k).length := by
    simpa only [onlinePreEpisodePlanningStages_length] using h.isLt
  simpa only [onlinePreEpisodePlanningStages, List.getElem_ofFn] using
    List.drop_eq_getElem_cons hi

/-- True environments of every planning suffix are the actual E suffix,
independently of the observations and episode index. -/
theorem onlinePreEpisodePlanningStages_suffix_environments {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k n : ℕ) :
    onlinePlanningEnvironments ((onlinePreEpisodePlanningStages E history k).drop n) =
      (List.ofFn E).drop n := by
  change ((onlinePreEpisodePlanningStages E history k).drop n).map
    (fun stage => stage.environment) = _
  rw [List.map_drop]
  change (onlinePlanningEnvironments (onlinePreEpisodePlanningStages E history k)).drop n = _
  rw [onlinePreEpisodePlanningStages_environments]

/-- The real observed-history event supplies the recursive certificates for
this exact pre-episode table, with the fixed true continuation and source cap. -/
theorem onlineObservedCertificates_imply_chronologicalCertificates
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (δ c₁ c₂ : ℝ)
    (hevent : onlineObservedPrefixBonusCertificates H K E
      (onlineTrueSuffixRowFamily E) δ c₁ c₂ history) (k : Fin K) :
    onlineChronologicalBonusCertificates (H : ℝ) (Real.log (1 / δ)) c₁ c₂
      (onlinePreEpisodePlanningStages E history k.val) := by
  apply onlineChronologicalCertificates_of_suffixHeads
  intro n stage tail hdrop
  have hlength := congrArg List.length hdrop
  simp only [List.length_drop, onlinePreEpisodePlanningStages_length,
    List.length_cons] at hlength
  have hn : n < H := by omega
  let h : Fin H := ⟨n, hn⟩
  have hcanonical := onlinePreEpisodePlanningStages_drop_stage E history k.val h
  rw [hdrop] at hcanonical
  have hs := (List.cons.inj hcanonical).1
  have ht := (List.cons.inj hcanonical).2
  subst stage
  subst tail
  have henv : onlinePlanningEnvironments
      ((onlinePreEpisodePlanningStages E history k.val).drop (n + 1)) =
      (List.ofFn E).drop (n + 1) := by
    exact onlinePreEpisodePlanningStages_suffix_environments E history k.val (n + 1)
  change onlinePlanningEnvironments
    ((onlinePreEpisodePlanningStages E history k.val).drop (h.val + 1)) =
    (List.ofFn E).drop (h.val + 1) at henv
  intro s a hnrow U hU
  have hU' : ∀ x, onlineTrueSuffixRowFamily E (h, (s, a)) x ≤ U x ∧
      U x ≤ (H : ℝ) := by
    simpa only [onlineTrueSuffixRowFamily, henv] using hU
  have hc := onlineObservedCertificates_imply_planningRowCertificate H K E history
    δ c₁ c₂ hevent k h s a hnrow U hU'
  simpa only [onlinePlanningHeadCertificate, onlineHistoryPlanningStage,
    onlineTrueSuffixRowFamily, henv] using hc

/-- Same transcript, same episode, all active suffix tables: deterministic
optimal Bellman V/Q dominance. The true optima are those of unchanged E.
Source trajectory and deployed-planner identifications remain separate. -/
theorem onlineObservedCertificates_imply_allStageBellmanOptimism
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (δ c₁ c₂ : ℝ)
    (hL : 1 ≤ Real.log (1 / δ)) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hevent : onlineObservedPrefixBonusCertificates H K E
      (onlineTrueSuffixRowFamily E) δ c₁ c₂ history) (k : Fin K) (h : Fin H) :
    (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val s) ∧
    (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
      onlineCappedBackwardQAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val s a) := by
  have hcert := onlineObservedCertificates_imply_chronologicalCertificates
    H K E history δ c₁ c₂ hevent k
  have hsuffix := onlineChronologicalCertificates_drop (H : ℝ) (Real.log (1 / δ))
    c₁ c₂ (onlinePreEpisodePlanningStages E history k.val) hcert h.val
  have hlen : (((onlinePreEpisodePlanningStages E history k.val).drop h.val).length : ℝ) ≤
      (H : ℝ) := by
    exact_mod_cast (show ((onlinePreEpisodePlanningStages E history k.val).drop h.val).length ≤ H by
      simp only [List.length_drop, onlinePreEpisodePlanningStages_length]
      omega)
  have hb := onlineCappedBackward_dominates_trueOptimal (H : ℝ)
    (Real.log (1 / δ)) c₁ c₂ (Nat.cast_nonneg _) hL hc₁ hc₂
    ((onlinePreEpisodePlanningStages E history k.val).drop h.val) hlen hsuffix
  rw [onlinePreEpisodePlanningStages_suffix_environments] at hb
  exact hb

end StatisticalRL.OnlineRL
