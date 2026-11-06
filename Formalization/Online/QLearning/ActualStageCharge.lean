import Formalization.Online.QLearning.ActualStageRecursion

namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

private theorem sum_fin_range (K : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin K, f k.val) = ∑ k ∈ Finset.range K, f k := by
  apply Finset.sum_bij (fun k _ => k.val)
  · intro k hk; exact Finset.mem_range.mpr k.isLt
  · intro k hk j hj he; exact Fin.ext he
  · intro k hk; exact ⟨⟨k,Finset.mem_range.mp hk⟩,Finset.mem_univ _,rfl⟩
  · intro k hk; rfl

theorem qLearning_actualStageVisitCount {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (k : Fin K) :
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    (qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)).length =
      onlineVisitCount rows k.val (rows k.val) := by
  dsimp only
  rw [qLearning_actualStage_visitList]
  rw [← qLearningRangeVisits_length]
  apply congrArg List.length
  apply List.filter_congr
  intro e he
  simp

/-- The source initialization charge specialized to actual pre-episode counts. -/
theorem qLearning_actualStageFirstVisit_budget {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) :
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    (∑ k : Fin K,
      onlineQRateWeight H
        (qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)).length 0*(H:ℝ)) ≤
      (Fintype.card (State×Action):ℝ)*(H:ℝ) := by
  classical
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  have h := qLearning_firstVisit_budget rows K H hH
  rw [← sum_fin_range] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [qLearning_actualStageVisitCount]

/-- The corrected zero-based β summation bound on the actual trajectory. -/
theorem qLearning_actualStageBeta_budget {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 0 ≤ cb)
    (path : OnlineOutcomePath.{u,0} State (K*H)) (h : Fin H) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    (∑ k : Fin K, qLearningSourceBeta H
      (qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)).length L cb) ≤
      8*cb*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ) := by
  classical
  letI : Nonempty State := ⟨fallback⟩
  letI : Nonempty Action := (E h).action_nonempty
  letI : Nonempty (Fin H) := ⟨h⟩
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  have hc : (1:ℝ) ≤ Fintype.card (OnlineMDPRow State Action H) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0<Fintype.card (OnlineMDPRow State Action H)))
  have hk : (1:ℝ) ≤ K := by exact_mod_cast (Nat.succ_le_iff.mpr hK)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    nlinarith
  have hb := qLearning_sourceBeta_visitBudget rows K H L cb hL hcb
  rw [← sum_fin_range] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [qLearning_actualStageVisitCount]

end StatisticalRL.OnlineRL
