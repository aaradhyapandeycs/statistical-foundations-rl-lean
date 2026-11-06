import Formalization.Online.QLearning.ActualStageVisitList

/-! The source propagation budget on the actual Q-learning stage visit lists. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualStagePropagation_budget {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (gap : ℕ → ℝ) (hgap : ∀ e, e<K → 0 ≤ gap e) :
    (∑ k : Fin K,
      let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
      let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
      let t := visits.length
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) ≤
      (1+1/(H:ℝ))*(∑ e : Fin K, gap e.val) := by
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  have hgen := qLearning_visitList_propagation_budget H hH rows K gap hgap
  have hleft : (∑ k : Fin K,
      let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
      let t := visits.length
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) =
      ∑ k ∈ Finset.range K,
        let visits := (List.range k).filter (fun e => rows e = rows k)
        let t := visits.length
        ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i) := by
    apply Finset.sum_bij (fun k _ => k.val)
    · intro k hk; exact Finset.mem_range.mpr k.isLt
    · intro k hk j hj he; exact Fin.ext he
    · intro k hk; exact ⟨⟨k,Finset.mem_range.mp hk⟩,Finset.mem_univ _,rfl⟩
    · intro k hk
      dsimp only
      rw [qLearning_actualStage_visitList]
  have hright : (∑ e : Fin K, gap e.val) = ∑ e ∈ Finset.range K, gap e := by
    apply Finset.sum_bij (fun e _ => e.val)
    · intro e he; exact Finset.mem_range.mpr e.isLt
    · intro e he j hj heq; exact Fin.ext heq
    · intro e he; exact ⟨⟨e,Finset.mem_range.mp he⟩,Finset.mem_univ _,rfl⟩
    · intro e he; rfl
  change (∑ k : Fin K,
      let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
      let t := visits.length
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) ≤ _
  rw [hleft,hright]
  convert hgen using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun vs : List ℕ =>
    ∑ i : Fin vs.length, onlineQRateWeight H vs.length (i.val+1)*gap (vs.get i))
  apply List.filter_congr
  intro e he
  simp
end StatisticalRL.OnlineRL
