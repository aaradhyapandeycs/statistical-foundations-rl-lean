import Formalization.Online.QLearning.ActualStageGap
import Formalization.Online.QLearning.GreedyPolicyOneStep

namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- Every recorded action is chosen by the actual policy fixed at episode start. -/
theorem qLearning_actualStageRow_greedy {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (k : Fin K) :
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
    (rows k.val).2 = qLearningChronologicalPolicy E table h (rows k.val).1 := by
  classical
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  let t := k.val*H+h.val
  have hlen : hist.length = K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
  have ht : t < hist.length := by rw [hlen]; dsimp [t]; have := h.isLt; have := k.isLt; nlinarith
  have ha := onlineTranscriptRowSequence_agrees (choose []) hist ⟨t,ht⟩
  have hc := onlineSequentialPathHistory_rows_consistent choose (K*H) [] (by simp [onlineTranscriptRowsConsistent]) path
  have hr : (hist.get ⟨t,ht⟩).1 = choose (hist.take t) := hc ⟨t,ht⟩
  have htag := qLearning_actualStageRow_tag hH E bonus initial fallback path h k.val k.isLt
  have heq : (h,rows k.val) = choose (hist.take t) := by
    calc
      (h,rows k.val) = onlineTranscriptRowSequence (choose []) hist t := htag.symm
      _ = (hist.get ⟨t,ht⟩).1 := ha
      _ = choose (hist.take t) := hr
  have htake : (hist.take t).length = t := by simp [List.length_take,Nat.min_eq_left ht.le]
  have hmod : t%H=h.val := by simp [t,Nat.add_mod,Nat.mod_eq_of_lt h.isLt]
  have hdiv : t/H=k.val := by
    dsimp [t]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hH, Nat.div_eq_of_lt h.isLt, zero_add]
  have hstage : (⟨(hist.take t).length%H,Nat.mod_lt _ hH⟩ : Fin H) = h := by
    apply Fin.ext
    change (hist.take t).length % H = h.val
    simpa only [htake] using hmod
  have hbefore : (hist.take t).take (((hist.take t).length/H)*H) = hist.take (k.val*H) := by
    rw [htake,hdiv,List.take_take,Nat.min_eq_left (Nat.le_add_right _ _)]
  have hp := congrArg (fun r : OnlineMDPRow State Action H => r.2) heq
  dsimp only [choose,onlineEpisodicChoose] at hp
  rw [hstage,hbefore] at hp
  have hs := congrArg Prod.fst hp
  have hac := congrArg Prod.snd hp
  change (rows k.val).2 = qLearningChronologicalPolicy E
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)) h (rows k.val).1
  rw [hs]
  exact hac

end StatisticalRL.OnlineRL
