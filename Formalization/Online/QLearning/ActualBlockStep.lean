import Formalization.Online.QLearning.ActualBlockSlice

/-! bridge from actual episode slices to the chronological
log. No concentration, source optimism, or desired list identity is assumed. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- The real target log after k completed episodes. -/
noncomputable def qLearningActualEpisodeLog {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : ℕ) (r : OnlineMDPRow State Action H) : List ℝ :=
  (qLearningLoggedVisitFold hH E bonus r (qLearningChronologicalInitial H)
    ((qLearningActualSequentialHistory hH E bonus initial fallback path).take (k*H))).2

/-- A real completed episode appends exactly its queried-stage target when
that stage visited r, and appends nothing otherwise. -/
theorem qLearningActualEpisodeLog_succ {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    qLearningActualEpisodeLog hH E bonus initial fallback path (k.val+1) r =
      qLearningActualEpisodeLog hH E bonus initial fallback path k.val r ++
        (if (qLearningActualBlockRecord hH E bonus initial fallback path k r.1).1 = r then
          [qLearningVisitTarget hH E bonus
            (qLearningChronologicalFold hH E bonus
              (qLearningActualTableAt hH E bonus initial fallback path (k.val*H))
              (qLearningActualBlockBefore hH E bonus initial fallback path k r.1))
            (qLearningActualBlockRecord hH E bonus initial fallback path k r.1)]
         else []) := by
  classical
  let history := qLearningActualSequentialHistory hH E bonus initial fallback path
  have hsplit : history.take ((k.val+1)*H) = history.take (k.val*H) ++
      (history.drop (k.val*H)).take H := by
    rw [show (k.val+1)*H = k.val*H+H by ring, List.take_add]
  have hblock := qLearningActualBlock_eq_slice hH E bonus initial fallback path k r.1
  have htarget := qLearningActualBlock_target hH E bonus initial fallback path k r
  unfold qLearningActualEpisodeLog
  change (qLearningLoggedVisitFold hH E bonus r (qLearningChronologicalInitial H)
    (history.take ((k.val+1)*H))).2 = _
  rw [hsplit, qLearningLoggedVisitFold_append, ← hblock]
  change _ ++ (qLearningLoggedVisitFold hH E bonus r
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H))
      (qLearningActualBlock hH E bonus initial fallback path k r.1)).2 = _
  rw [htarget]

end StatisticalRL.OnlineRL
