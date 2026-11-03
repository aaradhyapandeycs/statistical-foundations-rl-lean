import Formalization.Online.SourceOptimism.CappedBackwardOptimism
import Formalization.Online.SourceOptimism.ObservedPrefixEvent

/-! Same-data adapter from completed online transcript
to chronological capped-planning stages. No new sampling law or concentration
premise is introduced. Counts already include each recorded transition's update;
only episodes strictly before zero-based episode k are supplied to its planner. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- One chronological stage with the actual observed row lists. -/
noncomputable def onlineHistoryPlanningStage {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H) :
    OnlineObservedPlanningStage State Action where
  environment := E h
  observations s a := onlineRowOutcomes history (h, (s, a))

/-- Zero-based episode k uses exactly the first k*H recorded transitions.
Source episode k+1 follows all increments of the first k completed episodes. -/
noncomputable def onlinePreEpisodePlanningStages {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) :
    List (OnlineObservedPlanningStage State Action) :=
  List.ofFn (fun h => onlineHistoryPlanningStage E (history.take (k * H)) h)

/-- The chronological list has exactly the source horizon, including at k=0. -/
theorem onlinePreEpisodePlanningStages_length {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) :
    (onlinePreEpisodePlanningStages E history k).length = H := by
  simp [onlinePreEpisodePlanningStages]

/-- Known true environments are unchanged and independent of observed samples. -/
theorem onlinePreEpisodePlanningStages_environments {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) :
    onlinePlanningEnvironments (onlinePreEpisodePlanningStages E history k) =
      List.ofFn E := by
  simp [onlinePlanningEnvironments, onlinePreEpisodePlanningStages,
    onlineHistoryPlanningStage, List.map_ofFn, Function.comp_def]

/-- The count is exactly the number of recorded row outcomes; no current
unobserved transition or future episode is counted. -/
theorem onlineHistoryPlanningStage_count {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H)
    (s : State) (a : Action) :
    ((onlineHistoryPlanningStage E history h).observations s a).length =
      (onlineRowOutcomes history (h, (s, a))).length := rfl

/-- Recording one completed transition performs exactly the source count
increment in its row and leaves every other row count unchanged. The current
sample is recorded before subsequent planning uses the updated count. -/
theorem onlineObservedCount_append_transition {H : ℕ}
    (history : List (OnlineMDPRow State Action H × State))
    (row queried : OnlineMDPRow State Action H) (successor : State) :
    (onlineRowOutcomes (history ++ [(row, successor)]) queried).length =
      (onlineRowOutcomes history queried).length + if row = queried then 1 else 0 := by
  by_cases heq : row = queried
  · simp [onlineRowOutcomes, List.filterMap_append, heq]
  · simp [onlineRowOutcomes, List.filterMap_append, heq]

/-- Positive-count empirical rows agree on the exact chronological data and
count, including dependent Fin indices; there is no conditional iid claim. -/
theorem onlineHistoryPlanningStage_row_eq {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H)
    (s : State) (a : Action)
    (hpos : 0 < (onlineRowOutcomes history (h, (s, a))).length) :
    onlineObservedPlanningRow (onlineHistoryPlanningStage E history h) s a =
      FiniteDistribution.empiricalRow _ hpos
        (onlineObservedRowData history (h, (s, a))) := by
  simpa only [onlineHistoryPlanningStage, onlineObservedRowData] using
    onlineObservedPlanningRow_positive (onlineHistoryPlanningStage E history h) s a hpos

/-- Fixed true continuation used by the observed event: source stage h+1 is
zero-based stage h.val, so its next continuation drops h.val+1 stages. This
family contains no empirical value, episode index, or observed data. -/
noncomputable def onlineTrueSuffixRowFamily {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (r : OnlineMDPRow State Action H) : State → ℝ :=
  EnvironmentStage.optimalValue ((List.ofFn E).drop (r.1.val + 1))

/-- Consume precisely the real observed-prefix event at one stage/row, for any
continuation U in the required induction interval. This supplies a same-data
head certificate; recursive suffix bookkeeping remains separate. -/
theorem onlineObservedCertificates_imply_planningRowCertificate
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (δ c₁ c₂ : ℝ)
    (hevent : onlineObservedPrefixBonusCertificates H K E
      (onlineTrueSuffixRowFamily E) δ c₁ c₂ history)
    (k : Fin K) (h : Fin H) (s : State) (a : Action)
    (hn : 3 ≤ (onlineRowOutcomes (history.take (k.val * H)) (h, (s, a))).length)
    (U : State → ℝ)
    (hU : ∀ x, onlineTrueSuffixRowFamily E (h, (s, a)) x ≤ U x ∧ U x ≤ (H : ℝ)) :
    ((E h).transition s a).expectation (onlineTrueSuffixRowFamily E (h, (s, a))) ≤
      (onlineObservedPlanningRow
        (onlineHistoryPlanningStage E (history.take (k.val * H)) h) s a).expectation U +
      c₁ * Real.sqrt ((onlineObservedPlanningRow
        (onlineHistoryPlanningStage E (history.take (k.val * H)) h) s a).variance U *
        (Real.log (1 / δ) /
          (onlineRowOutcomes (history.take (k.val * H)) (h, (s, a))).length)) +
      c₂ * (H : ℝ) * (Real.log (1 / δ) /
        (onlineRowOutcomes (history.take (k.val * H)) (h, (s, a))).length) := by
  have hpos : 0 < (onlineRowOutcomes (history.take (k.val * H)) (h, (s, a))).length := by
    omega
  rw [onlineHistoryPlanningStage_row_eq E (history.take (k.val * H)) h s a hpos]
  exact hevent k (h, (s, a)) hn U hU

end StatisticalRL.OnlineRL
