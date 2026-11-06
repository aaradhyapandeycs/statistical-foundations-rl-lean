import Formalization.Online.QLearning.ActualPolicyGapRange
import Formalization.Online.Predictable.OnlinePredictableObservedProcess

/-! Actual Q-learning policy-gap residuals are predictable-test residuals
under the actual reset/prefix law. Source: onlineRL.tex:2200–2216, 2380–2395. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance regretResidualStateMeasurable : MeasurableSpace State := ⊤
attribute [local instance] Classical.propDecidable

/-- The test function uses only the table from completed episodes. -/
noncomputable def qLearningRegretTailAtPrefix {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (k : ℕ) (h : Fin H) (history : List (OnlineMDPRow State Action H × State)) : State → ℝ :=
  qLearningGreedyPolicyOptimalityGap E
    (qLearningChronologicalFold hH E bonus (qLearningChronologicalInitial H) (history.take (k*H)))
    (h.val+1)

noncomputable def qLearningActualRegretResidual {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (fallback : State) (k : Fin K) (h : Fin H)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  let rows := qLearningActualStageRowSequence hH E bonus sample.1 fallback sample.2 h
  let table := qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)
  let hist := qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2
  let next := (hist.map Prod.snd).getD (k.val*H+h.val) fallback
  qLearningGreedyPolicyResidual E table (h,rows k.val) next

/-- The explicit source P−sample residual equals the observable predictable
process, using the real stored row and successor of the same transcript. -/
theorem qLearning_actualRegretResidual_eq_observed {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (fallback : State) (k : Fin K) (h : Fin H)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :
    qLearningActualRegretResidual hH E bonus fallback k h sample =
      onlinePredictableObservedY H K (K*H) hH E fallback (qLearningActualEpisodePlanner hH E bonus)
        (k.val*H+h.val) (fun (_initial : Fin K → State) history =>
          qLearningRegretTailAtPrefix hH E bonus k.val h history) sample := by
  classical
  let planner := qLearningActualEpisodePlanner hH E bonus
  let hist := qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2
  let choose := onlineEpisodicChoose H K hH sample.1 fallback planner
  let n := k.val*H+h.val
  have hn : n < hist.length := by
    have hlen : hist.length=K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
    rw [hlen]
    dsimp [n]
    have := k.isLt
    have := h.isLt
    nlinarith
  let record := hist.get ⟨n,hn⟩
  let θ := fun (_initial : Fin K → State) history => qLearningRegretTailAtPrefix hH E bonus k.val h history
  have hlen : (hist.take n).length=n := by simp [List.length_take,Nat.min_eq_left hn.le]
  have hobs : (onlineT3CommonPrefixObservation H K (K*H) hH fallback planner (n+1) sample).2 =
      hist.take n ++ [(record.1,record.2)] := by
    simpa only [record,Prod.mk.eta] using (List.take_concat_get' hist n hn).symm
  have hread := onlinePredictableTestFromObservedPrefix_append H K E n θ (hist.take n)
    record.1 record.2 (onlineT3CommonPrefixObservation H K (K*H) hH fallback planner (n+1) sample) hlen hobs
  have hrow : record.1 = (h,qLearningActualStageRowSequence hH E bonus sample.1 fallback sample.2 h k.val) := by
    have ha := onlineTranscriptRowSequence_agrees (choose []) hist ⟨n,hn⟩
    have ht := qLearning_actualStageRow_tag hH E bonus sample.1 fallback sample.2 h k.val k.isLt
    exact ha.symm.trans ht
  have hnext : (hist.map Prod.snd).getD n fallback=record.2 := by
    have hn' : n < (hist.map Prod.snd).length := by simpa using hn
    rw [List.getD_eq_get _ fallback ⟨n,hn'⟩]
    simp only [List.get_eq_getElem,List.getElem_map,record]
  have htail : θ sample.1 (hist.take n) =
      qLearningGreedyPolicyOptimalityGap E
        (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)) (h.val+1) := by
    dsimp only [θ,qLearningRegretTailAtPrefix,qLearningActualTableAt]
    rw [List.take_take,Nat.min_eq_left (Nat.le_add_right _ _)]
  change qLearningActualRegretResidual hH E bonus fallback k h sample =
    onlinePredictableTestFromObservedPrefix H K E n θ
      (onlineT3CommonPrefixObservation H K (K*H) hH fallback planner (n+1) sample)
  rw [hread]
  change qLearningActualRegretResidual hH E bonus fallback k h sample =
    (onlineMDPSuccessorRowLaw E record.1).expectation (θ sample.1 (hist.take n)) -
      θ sample.1 (hist.take n) record.2
  rw [htail,hrow]
  dsimp only [qLearningActualRegretResidual,qLearningGreedyPolicyResidual]
  rw [hnext]

/-- Conditional centering follows from the actual sequential law and the
reset-vector/transcript-prefix sigma-field; no centering premise is assumed. -/
theorem qLearning_actualRegretResidual_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (bonus : ℕ → ℝ) (fallback : State)
    (k : Fin K) (h : Fin H) :
    let planner := qLearningActualEpisodePlanner hH E bonus
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    μ[qLearningActualRegretResidual hH E bonus fallback k h |
      onlineT3CommonPrefixSigma H K (K*H) hH fallback planner (k.val*H+h.val)] =ᵐ[μ] 0 := by
  let n := k.val*H+h.val
  let m := K*H-n-1
  have hn : n<K*H := by dsimp [n]; have := k.isLt; have := h.isLt; nlinarith
  have hT : K*H=(m+1)+n := by dsimp [m]; omega
  have hfun : qLearningActualRegretResidual hH E bonus fallback k h =
      onlinePredictableObservedY H K (K*H) hH E fallback (qLearningActualEpisodePlanner hH E bonus)
        n (fun (_initial : Fin K → State) history => qLearningRegretTailAtPrefix hH E bonus k.val h history) := by
    funext sample
    exact qLearning_actualRegretResidual_eq_observed hH E bonus fallback k h sample
  rw [hfun]
  exact onlinePredictableObservedY_condExp_zero H K (K*H) hH E ρ fallback
    (qLearningActualEpisodePlanner hH E bonus) n m hT _

/-- Adaptation is to the revealed prefix including this new successor. -/
theorem qLearning_actualRegretResidual_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (bonus : ℕ → ℝ) (fallback : State) (k : Fin K) (h : Fin H) :
    Measurable[onlineT3CommonPrefixSigma H K (K*H) hH fallback
      (qLearningActualEpisodePlanner hH E bonus) (k.val*H+h.val+1)]
      (qLearningActualRegretResidual hH E bonus fallback k h) := by
  have heq : qLearningActualRegretResidual hH E bonus fallback k h =
      onlinePredictableObservedY H K (K*H) hH E fallback (qLearningActualEpisodePlanner hH E bonus)
        (k.val*H+h.val) (fun (_initial : Fin K → State) history =>
          qLearningRegretTailAtPrefix hH E bonus k.val h history) := by
    funext sample
    exact qLearning_actualRegretResidual_eq_observed hH E bonus fallback k h sample
  rw [heq]
  exact onlinePredictableObservedY_measurable_next H K (K*H) hH E fallback
    (qLearningActualEpisodePlanner hH E bonus) (k.val*H+h.val) _

/-- The real conditional increment has the pointwise source range. -/
theorem qLearning_actualRegretResidual_abs_le {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (fallback : State) (k : Fin K) (h : Fin H)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :
    |qLearningActualRegretResidual hH E bonus fallback k h sample| ≤ (H:ℝ) := by
  exact qLearning_greedyPolicyResidual_abs_le hH E _ _ _

end StatisticalRL.OnlineRL
