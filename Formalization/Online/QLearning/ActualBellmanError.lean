import Formalization.Online.QLearning.WeightedBellmanAlgebra

/-! Exact actual Q error decomposition; no optimism or noise event premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearningActualEpisode_bellmanError {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r =
      onlineQRateWeight H t 0 * ((H:ℝ)-qLearningTrueOptimalQ E r) +
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
        ((qLearningChronologicalValue hH E
            (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
            (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
          (qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback)) +
         ((qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
          (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r)) + bonus (i.val+1)) := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let t := visits.length
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let w : Fin t → ℝ := fun i => onlineQRateWeight H t (i.val+1)
  let v : Fin t → ℝ := fun i => qLearningChronologicalValue hH E
    (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
    (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback)
  let u : Fin t → ℝ := fun i => (qLearningTrueOptimalNext E r)
    ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback)
  let b : Fin t → ℝ := fun i => bonus (i.val+1)
  let P := (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r)
  have hnorm : onlineQRateWeight H t 0 + ∑ i, w i = 1 := qLearning_rate_fin_normalized hH t
  have ha := qLearning_weightedBellman_subtract w (onlineQRateWeight H t 0) H
    ((E r.1).reward r.2.1 r.2.2) P v u b hnorm
  have hw := qLearningActualEpisode_weighted_fin hH E bonus initial fallback path k r
  dsimp only [qLearningTrueOptimalQ,onlineMDPSuccessorRowLaw] at ha ⊢
  dsimp only [visits,t,hist,w,v,u,b,P] at ha hw ⊢
  rw [hw]
  exact ha
end StatisticalRL.OnlineRL
