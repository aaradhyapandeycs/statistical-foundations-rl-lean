import Formalization.Online.QLearning.ActualRegretDefinitions
import Formalization.Online.QLearning.ActualStageCharge
import Formalization.Online.QLearning.ActualResidualCentering

/-! The stage recursion is on the actual state selector, so its next-stage
term can be iterated through the horizon with the same episode policies. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

noncomputable def qLearningActualEpisodePolicyError {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (n : ℕ) : ℝ :=
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  ∑ k : Fin K,
    let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
    let s := onlineEpisodicCurrentState H K initial fallback (hist.take (k.val*H+n))
    qLearningChronologicalValue hH E table n s - qLearningGreedyTruePolicyValue E table n s

theorem qLearning_actualStageRow_state {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (k : Fin K) :
    (qLearningActualStageRowSequence hH E bonus initial fallback path h k.val).1 =
      onlineEpisodicCurrentState H K initial fallback
        ((qLearningActualSequentialHistory hH E bonus initial fallback path).take (k.val*H+h.val)) := by
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  have hn : k.val*H+h.val<hist.length := by
    have hlen : hist.length=K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
    rw [hlen]
    have := k.isLt
    have := h.isLt
    nlinarith
  have hr := onlineSequentialEpisode_actual_row H K hH E initial fallback
    (qLearningActualEpisodePlanner hH E bonus) path k h
  have ha := onlineTranscriptRowSequence_agrees (choose []) hist ⟨k.val*H+h.val,hn⟩
  have ht := qLearning_actualStageRow_tag hH E bonus initial fallback path h k.val k.isLt
  have heq : (h,qLearningActualStageRowSequence hH E bonus initial fallback path h k.val) =
      (hist.get ⟨k.val*H+h.val,hn⟩).1 := ht.symm.trans ha
  exact (congrArg (fun r : OnlineMDPRow State Action H => r.2.1) (heq.trans hr))

theorem qLearning_actualEpisodePolicyError_terminal {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H)) :
    qLearningActualEpisodePolicyError hH E bonus initial fallback path H = 0 := by
  unfold qLearningActualEpisodePolicyError
  apply Finset.sum_eq_zero
  intro k hk
  dsimp only
  have hdrop : (onlineFixedPolicyStages E
      (qLearningChronologicalPolicy E (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)))).drop H = [] := by
    apply List.drop_eq_nil_of_le
    simp [onlineFixedPolicyStages]
  simp only [qLearningChronologicalValue,dif_neg (lt_irrefl H),qLearningGreedyTruePolicyValue,
    hdrop,DecisionStage.trajectoryValue_nil,sub_self]

/-- Recorded successors and actual next selector states give the same next
value error. At the episode boundary both continuations are truly zero. -/
theorem qLearning_actualEpisodePolicyError_next {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) :
    qLearningActualEpisodePolicyError hH E bonus initial fallback path (h.val+1) =
      let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
      ∑ k : Fin K,
        let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
        let next := (hist.map Prod.snd).getD (k.val*H+h.val) fallback
        qLearningChronologicalValue hH E table (h.val+1) next -
          qLearningGreedyTruePolicyValue E table (h.val+1) next := by
  classical
  unfold qLearningActualEpisodePolicyError
  dsimp only
  apply Finset.sum_congr rfl
  intro k hk
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  have hn : k.val*H+h.val<hist.length := by
    have hlen : hist.length=K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
    rw [hlen]
    have := k.isLt
    have := h.isLt
    nlinarith
  by_cases hh : h.val+1<H
  · have hs := onlineSequentialEpisode_successor_state H K hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) path k h hh
    have hnext : (hist.map Prod.snd).getD (k.val*H+h.val) fallback = (hist.get ⟨k.val*H+h.val,hn⟩).2 := by
      have hm : k.val*H+h.val<(hist.map Prod.snd).length := by simpa using hn
      rw [List.getD_eq_get _ fallback ⟨k.val*H+h.val,hm⟩]
      simp only [List.get_eq_getElem,List.getElem_map]
    dsimp only [hist,qLearningActualSequentialHistory] at hnext
    dsimp only [qLearningActualSequentialHistory]
    rw [hs,hnext]
  · have hlast : h.val+1=H := by have := h.isLt; omega
    have hdrop : (onlineFixedPolicyStages E
        (qLearningChronologicalPolicy E (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)))).drop (h.val+1)=[] := by
      rw [hlast]
      apply List.drop_eq_nil_of_le
      simp [onlineFixedPolicyStages]
    simp only [qLearningChronologicalValue,dif_neg hh,qLearningGreedyTruePolicyValue,hdrop,
      DecisionStage.trajectoryValue_nil,sub_self]

/-- The episode-zero stage uses exactly that episode's reset coordinate. -/
theorem qLearning_actualEpisodePolicyError_zero {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H)) :
    qLearningActualEpisodePolicyError hH E bonus initial fallback path 0 =
      ∑ k : Fin K,
        let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
        qLearningChronologicalValue hH E table 0 (initial k) -
          qLearningGreedyTruePolicyValue E table 0 (initial k) := by
  classical
  unfold qLearningActualEpisodePolicyError
  dsimp only
  apply Finset.sum_congr rfl
  intro k hk
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  have hlen : hist.length=K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
  have ht : (hist.take (k.val*H)).length=k.val*H := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.mul_le_mul_right H k.isLt.le)]
  have hs := onlineEpisodicCurrentState_reset H K hH initial fallback (hist.take (k.val*H)) k ht
  dsimp only [hist] at hs
  simp only [Nat.add_zero]
  rw [hs]

theorem qLearning_actualRegret_mem_Icc {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H)) :
    qLearningActualRegret hH E bonus initial fallback path ∈ Set.Icc 0 ((K:ℝ)*(H:ℝ)) := by
  have hp (k : Fin K) := qLearning_greedyPolicyOptimalityGap_mem_Icc hH E
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)) 0 (initial k)
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    exact (hp k).1
  · calc
      _ ≤ ∑ _k : Fin K, (H:ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hp k).2
      _ = (K:ℝ)*(H:ℝ) := by simp

/-- The source horizon recursion, with the actual first-visit and corrected
zero-based bonus bounds already discharged on the same transcript. -/
theorem qLearning_actual_episodePolicyError_stage_bound {H K : ℕ}
    (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 0 ≤ cb)
    (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path)) (h : Fin H) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    qLearningActualEpisodePolicyError hH E bonus initial fallback path h.val ≤
      (Fintype.card (State×Action):ℝ)*(H:ℝ) +
      (1+1/(H:ℝ))*qLearningActualEpisodePolicyError hH E bonus initial fallback path (h.val+1) +
      8*cb*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ) +
      ∑ k : Fin K, qLearningActualRegretResidual hH E bonus fallback k h (initial,path) := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  let table := fun k : Fin K => qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
  let visits := fun k : Fin K => qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let next := fun k : Fin K => (hist.map Prod.snd).getD (k.val*H+h.val) fallback
  let current := fun k : Fin K => qLearningChronologicalValue hH E (table k) h.val (rows k.val).1 -
    qLearningGreedyTruePolicyValue E (table k) h.val (rows k.val).1
  let future := fun k : Fin K => qLearningChronologicalValue hH E (table k) (h.val+1) (next k) -
    qLearningGreedyTruePolicyValue E (table k) (h.val+1) (next k)
  let init := fun k : Fin K => onlineQRateWeight H (visits k).length 0*(H:ℝ)
  let beta := fun k : Fin K => qLearningSourceBeta H (visits k).length L cb
  let residual := fun k : Fin K => qLearningActualRegretResidual hH E bonus fallback k h (initial,path)
  have hcurrent : qLearningActualEpisodePolicyError hH E bonus initial fallback path h.val =
      ∑ k : Fin K, current k := by
    unfold qLearningActualEpisodePolicyError
    dsimp only
    apply Finset.sum_congr rfl
    intro k hk
    have hs := qLearning_actualStageRow_state hH E bonus initial fallback path h k
    change qLearningChronologicalValue hH E (table k) h.val _ -
      qLearningGreedyTruePolicyValue E (table k) h.val _ = current k
    dsimp only [current]
    rw [hs]
  have hfuture : qLearningActualEpisodePolicyError hH E bonus initial fallback path (h.val+1) =
      ∑ k : Fin K, future k :=
    qLearning_actualEpisodePolicyError_next hH E bonus initial fallback path h
  have hstage : (∑ k : Fin K, current k) ≤ (∑ k : Fin K, init k) +
      (1+1/(H:ℝ))*(∑ k : Fin K, future k) + (∑ k : Fin K, beta k) +
      (∑ k : Fin K, residual k) :=
    qLearning_actual_stage_recursion hH E initial fallback δ cb path hgood h
  have hinit : (∑ k : Fin K, init k) ≤ (Fintype.card (State×Action):ℝ)*(H:ℝ) :=
    qLearning_actualStageFirstVisit_budget hH E bonus initial fallback path h
  have hbeta : (∑ k : Fin K, beta k) ≤
      8*cb*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ) :=
    qLearning_actualStageBeta_budget hH hK E initial fallback δ cb hδ hδ1 hcb path h
  rw [← hcurrent,← hfuture] at hstage
  change qLearningActualEpisodePolicyError hH E bonus initial fallback path h.val ≤
    (Fintype.card (State×Action):ℝ)*(H:ℝ) +
      (1+1/(H:ℝ))*qLearningActualEpisodePolicyError hH E bonus initial fallback path (h.val+1) +
      8*cb*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card (State×Action):ℝ)*Real.sqrt (K:ℝ) +
      (∑ k : Fin K, residual k)
  linarith

end StatisticalRL.OnlineRL
