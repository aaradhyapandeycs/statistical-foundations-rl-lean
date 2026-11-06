import Formalization.Online.QLearning.VisitListPropagation
import Formalization.Online.QLearning.ActualGreedyChoice

/-! Stagewise actual Q-learning rows and their ordered past visits. -/
namespace StatisticalRL.OnlineRL
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

noncomputable def qLearningActualStageRowSequence {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) : ℕ → State × Action :=
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  fun e => (onlineTranscriptRowSequence (choose []) hist (e*H+h.val)).2

theorem qLearning_actualStageRow_tag {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (e : ℕ) (he : e<K) :
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
    onlineTranscriptRowSequence (choose []) hist (e*H+h.val) =
      (h,qLearningActualStageRowSequence hH E bonus initial fallback path h e) := by
  classical
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  have hlen : hist.length = K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
  have hj : e*H+h.val < hist.length := by
    rw [hlen]
    have hh := h.isLt
    nlinarith
  have ha := onlineTranscriptRowSequence_agrees (choose []) hist ⟨e*H+h.val,hj⟩
  have ht := qLearningActualSequentialHistory_stage hH E bonus initial fallback path ⟨e*H+h.val,hj⟩
  have htag : (onlineTranscriptRowSequence (choose []) hist (e*H+h.val)).1 = h := by
    apply Fin.ext
    rw [ha]
    simpa [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt] using ht
  apply Prod.ext
  · exact htag
  · rfl

theorem qLearning_actualStage_visitList {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (h : Fin H) (k : Fin K) :
    qLearningActualVisitEpisodes hH E bonus initial fallback path k
      (h,qLearningActualStageRowSequence hH E bonus initial fallback path h k.val) =
    (List.range k.val).filter (fun e => qLearningActualStageRowSequence hH E bonus initial fallback path h e =
      qLearningActualStageRowSequence hH E bonus initial fallback path h k.val) := by
  classical
  unfold qLearningActualVisitEpisodes
  apply List.filter_congr
  intro e he
  have heK : e<K := (List.mem_range.mp he).trans k.isLt
  have heq := qLearning_actualStageRow_tag hH E bonus initial fallback path h e heK
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let rowAt := onlineTranscriptRowSequence (choose []) hist
  change decide (rowAt (e*H+h.val) = (h,(rowAt (k.val*H+h.val)).2)) =
    decide ((rowAt (e*H+h.val)).2 = (rowAt (k.val*H+h.val)).2)
  congr 1
  apply propext
  constructor
  · intro hh
    have hs := congrArg (fun p : OnlineMDPRow State Action H => p.2) hh
    exact hs
  · intro hh
    change rowAt (e*H+h.val) = (h,(rowAt (e*H+h.val)).2) at heq
    rw [heq]
    exact Prod.ext rfl hh
end StatisticalRL.OnlineRL
