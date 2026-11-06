import Formalization.Online.QLearning.ActualVisitOutcome

/-! Actual ordered-episode expression of the optimal-value weighted noise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualEpisodeIndexed_noise_bound {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) (δ : ℝ)
    (hgood : qLearningObservedOptimalNoiseGood E fallback δ
      (initial,qLearningActualSequentialHistory hH E bonus initial fallback path))
    (ht : 0 < (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      ((qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
        (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r))| ≤
    Real.sqrt ((H:ℝ)^3/(t:ℝ)*Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)) := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let t := visits.length
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  have h := qLearning_actualVisitCount_noise_bound hH E bonus initial fallback path k r δ hgood ht
  have heq : (∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) t i
        (fun x => (onlineRowOutcomes hist r).getD x.val fallback)) =
      (∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      ((qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
        (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hnext := qLearning_actualVisitOutcome_eq_rowPrefix hH E bonus initial fallback path k r i
    simp only [FiniteDistribution.centeredSample]
    rw [hnext]
  change |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) t i
        (fun x => (onlineRowOutcomes hist r).getD x.val fallback)| ≤ _ at h
  rw [heq] at h
  exact h
end StatisticalRL.OnlineRL
