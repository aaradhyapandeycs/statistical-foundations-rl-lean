import Formalization.Online.QLearning.TargetLogAppend

/-! exact endpoint specification, not a proof declaration. -/
namespace StatisticalRL.OnlineRL
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]

/-- The source's chronological episode targets, indexed by actual visits. -/
noncomputable def qLearningActualEpisodeTargets {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) : List ℝ := by
  classical
  exact (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).filterMap (fun e =>
    if he : e < K then some (qLearningEpisodeTargetAt hH E bonus initial fallback path r ⟨e,he⟩)
    else none)

/-- Exact unresolved target. Every parameter is actual model/path data; no
assumed recurrence, concentration, trajectory certificate, or reset law. -/
def qLearningActualTargetListIdentity : Prop :=
  ∀ {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H),
    (qLearningLoggedVisitFold hH E bonus r (qLearningChronologicalInitial H)
      ((qLearningActualSequentialHistory hH E bonus initial fallback path).take (k.val*H))).2 =
    qLearningActualEpisodeTargets hH E bonus initial fallback path k r

end StatisticalRL.OnlineRL
