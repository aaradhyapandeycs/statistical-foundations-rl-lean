import Formalization.Online.QLearning.EpisodeSourceNoise
import Formalization.Online.QLearning.TerminalZeroNoise

/-! Source-log ordered-episode noise bound including H=1 terminal zero. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualEpisode_sourceNoise {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgood : qLearningObservedOptimalNoiseGood E fallback δ
      (initial,qLearningActualSequentialHistory hH E bonus initial fallback path))
    (ht : 0 < (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      ((qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
        (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r))| ≤
    2*Real.sqrt ((H:ℝ)^3/(t:ℝ)*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)) := by
  classical
  by_cases hH1 : H=1
  · have hr : r.1.val+1 = H := by have hh := r.1.isLt; omega
    have hz := qLearningTrueOptimalNext_last_zero E r hr
    simp [hz,FiniteDistribution.expectation_const]
  · have hH2 : 2 ≤ H := by omega
    exact qLearning_actualEpisode_sourceNoise_nonterminal hH hH2 E bonus initial fallback path k r δ hδ hδ1 hgood ht
end StatisticalRL.OnlineRL
