import Formalization.Online.QLearning.ObservedOptimalConfidence
import Formalization.Online.QLearning.VisitRank

/-! Deterministic consumption of the simultaneous transcript event at an
actual pre-episode visit count. No random-count independence premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualVisitCount_noise_bound {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) (δ : ℝ)
    (hgood : qLearningObservedOptimalNoiseGood E fallback δ
      (initial,qLearningActualSequentialHistory hH E bonus initial fallback path))
    (ht : 0 < (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let t := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length
    |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) t i
        (fun x => (onlineRowOutcomes (qLearningActualSequentialHistory hH E bonus initial fallback path) r).getD x.val fallback)| ≤
    Real.sqrt ((H:ℝ)^3/(t:ℝ)*Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)) := by
  classical
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let t := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length
  have hle : t ≤ k.val := by
    dsimp [t,qLearningActualVisitEpisodes]
    exact (List.length_filter_le _ _).trans_eq List.length_range
  have htK : t ≤ K := hle.trans k.isLt.le
  have hpre : t = (onlineRowOutcomes (hist.take (k.val*H)) r).length := by
    have h := (qLearningActualVisitEpisodes_length hH E bonus initial fallback path k r).1
    simpa [t,hist,qLearningActualTableAt,qLearningChronologicalFold_count,
      qLearningChronologicalInitial,qLearningRowVisits_length_eq_outcomes] using h
  have htotal : t ≤ (onlineRowOutcomes hist r).length := by
    rw [hpre]
    have hs := congrArg (fun xs => onlineRowOutcomes xs r) (List.take_append_drop (k.val*H) hist).symm
    simp only [onlineRowOutcomes, List.filterMap_append] at hs
    change (List.filterMap (fun pair => if pair.1=r then some pair.2 else none) (hist.take (k.val*H))).length ≤
      (List.filterMap (fun pair => if pair.1=r then some pair.2 else none) hist).length
    rw [hs, List.length_append]
    omega
  change |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
    (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) t i
      (fun x => (onlineRowOutcomes hist r).getD x.val fallback)| ≤
    Real.sqrt ((H:ℝ)^3/(t:ℝ)*Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))
  cases htv : t with
  | zero => simp [t,htv] at ht
  | succ m =>
      have hmK : m < K := by omega
      have hm : m+1 ≤ (onlineRowOutcomes hist r).length := by omega
      have hb := hgood r ⟨m,hmK⟩ hm
      simpa only [hist, Nat.cast_add, Nat.cast_one] using hb
end StatisticalRL.OnlineRL
