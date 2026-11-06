import Formalization.Online.QLearning.TrueOptimalQ

/-! Actual Q expansion in finite ordered-visit indexing. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearningActualEpisode_weighted_fin {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r =
      onlineQRateWeight H t 0 * H +
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
        ((E r.1).reward r.2.1 r.2.2 +
          qLearningChronologicalValue hH E
            (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
            (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) + bonus (i.val+1)) := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let t := visits.length
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let targets := qLearningActualEpisodeTargets hH E bonus initial fallback path k r
  have hlen : targets.length = t := qLearning_episodeTargets_length hH E bonus initial fallback path k r
  have hw := qLearningActualEpisode_weighted hH E bonus initial fallback path k r
  change (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r =
    onlineQRateWeight H targets.length 0 * H +
      ∑ i ∈ Finset.Icc 1 targets.length, onlineQRateWeight H targets.length i * targets.getD (i-1) 0 at hw
  rw [hlen] at hw
  have heq : (∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      ((E r.1).reward r.2.1 r.2.2 +
        qLearningChronologicalValue hH E
          (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
          (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) + bonus (i.val+1))) =
      ∑ j ∈ Finset.Icc 1 t, onlineQRateWeight H t j * targets.getD (j-1) 0 := by
    apply Finset.sum_bij (fun i _ => i.val+1)
    · intro i hi; simp only [Finset.mem_Icc]; omega
    · intro i hi j hj hij; apply Fin.ext; omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨⟨j-1,by omega⟩,Finset.mem_univ _,?_⟩
      simp only
      omega
    · intro i hi
      have hget := qLearning_episodeTargets_getD hH E bonus initial fallback path k r i
      have hrank := qLearningActualEpisodeTarget_ranked hH E bonus initial fallback path k r i
      dsimp only at hget hrank
      simp only [Nat.add_sub_cancel]
      rw [hget,hrank]
  rw [← heq] at hw
  exact hw
end StatisticalRL.OnlineRL
