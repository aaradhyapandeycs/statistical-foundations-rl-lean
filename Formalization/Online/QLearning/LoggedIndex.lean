import Formalization.Online.QLearning.VisitIndices
import Mathlib.Data.List.GetD

/-! log-index bridge. The target function below explicitly
folds the same observed prefix before reading the recorded successor. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- The target actually consumed at chronological time j. -/
noncomputable def qLearningTargetAtRecord {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (history : List (OnlineMDPRow State Action H × State))
    (j : Fin history.length) : ℝ :=
  qLearningVisitTarget hH E bonus
    (qLearningChronologicalFold hH E bonus table (history.take j.val)) (history.get j)

/-- Record numbering on a chronological pre-episode history. The proof must
be by snoc induction using `qLearningLogFrom_snoc`; it does not assume a target
identity. This candidate intentionally stops at the definitions until its
finite-index transport is proved. -/
noncomputable def qLearningEpisodeTargetAt {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (r : OnlineMDPRow State Action H) (e : Fin K) : ℝ :=
  let history := qLearningActualSequentialHistory hH E bonus initial fallback path
  let j := e.val*H+r.1.val
  let current := qLearningActualTableAt hH E bonus initial fallback path j
  let pre := qLearningActualTableAt hH E bonus initial fallback path (e.val*H)
  let successor := (history.map Prod.snd).getD j fallback
  (E r.1).reward r.2.1 r.2.2 +
    qLearningChronologicalValue hH E pre (r.1.val+1) successor + bonus (current.count r+1)

/-- At a real visit to r, its chronological target equals the source
pre-episode continuation and uses the actual pre-update count plus one. -/
theorem qLearningEpisodeTargetAt_eq_actual {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (r : OnlineMDPRow State Action H) (e : Fin K)
    (hj : e.val*H+r.1.val <
      (qLearningActualSequentialHistory hH E bonus initial fallback path).length)
    (hrow : ((qLearningActualSequentialHistory hH E bonus initial fallback path).get
      ⟨e.val*H+r.1.val,hj⟩).1 = r) :
    qLearningTargetAtRecord hH E bonus (qLearningChronologicalInitial H)
      (qLearningActualSequentialHistory hH E bonus initial fallback path) ⟨e.val*H+r.1.val,hj⟩ =
    qLearningEpisodeTargetAt hH E bonus initial fallback path r e := by
  classical
  have hlocal := qLearningActualWithinEpisode_value hH E bonus initial fallback path e r.1
    (((qLearningActualSequentialHistory hH E bonus initial fallback path).get
      ⟨e.val*H+r.1.val,hj⟩).2)
  simp only [qLearningActualTableAt] at hlocal
  simp only [qLearningTargetAtRecord, qLearningEpisodeTargetAt, qLearningActualTableAt,
    qLearningVisitTarget, hrow]
  rw [hlocal]
  simp [List.getD_eq_getElem, hj]

end StatisticalRL.OnlineRL
