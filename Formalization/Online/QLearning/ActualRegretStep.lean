import Formalization.Online.QLearning.ActualRegretDefinitions
import Formalization.Online.QLearning.ActualGreedyRow

/-! Source onlineRL.tex:2180–2216, using the real pre-episode policy and
recorded next state. The residual below is an explicit transition residual;
its conditional centering is a separate probability obligation. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- The source optimal-policy continuation difference in the same environment. -/
noncomputable def qLearningGreedyPolicyOptimalityGap {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (n : ℕ) (s : State) : ℝ :=
  EnvironmentStage.optimalValue ((List.ofFn E).drop n) s -
    qLearningGreedyTruePolicyValue E table n s

/-- The source transition fluctuation: P of the past-selected function minus
its value at the newly observed successor. -/
noncomputable def qLearningGreedyPolicyResidual {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (r : OnlineMDPRow State Action H) (next : State) : ℝ :=
  (onlineMDPSuccessorRowLaw E r).expectation
    (qLearningGreedyPolicyOptimalityGap E table (r.1.val+1)) -
      qLearningGreedyPolicyOptimalityGap E table (r.1.val+1) next

/-- Actual Q-learning's source one-step regret recursion on its simultaneous
5.18 event. The policy, earlier visits, values, transition row, and successor
all come from the same actual sequential transcript. -/
theorem qLearning_actual_regret_oneStep {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path))
    (h : Fin H) (k : Fin K) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    let r : OnlineMDPRow State Action H := (h,rows k.val)
    let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    let next := (hist.map Prod.snd).getD (k.val*H+h.val) fallback
    let gap := qLearningActualStageGap hH E bonus initial fallback path h
    qLearningChronologicalValue hH E table h.val r.2.1 -
      qLearningGreedyTruePolicyValue E table h.val r.2.1 ≤
      onlineQRateWeight H t 0*(H:ℝ) +
        (∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) +
        qLearningSourceBeta H t L cb +
        qLearningGreedyPolicyOptimalityGap E table (h.val+1) next +
        qLearningGreedyPolicyResidual E table r next := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  let r : OnlineMDPRow State Action H := (h,rows k.val)
  let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let t := visits.length
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let next := (hist.map Prod.snd).getD (k.val*H+h.val) fallback
  let gap := qLearningActualStageGap hH E bonus initial fallback path h
  have hgreedy := qLearning_actualStageRow_greedy hH E bonus initial fallback path h k
  have hrow : (h,(r.2.1,qLearningChronologicalPolicy E table h r.2.1)) = r := by
    dsimp only [r]
    rw [← hgreedy]
  have hstep := qLearning_greedyPolicy_oneStep hH E table h r.2.1
  change qLearningChronologicalValue hH E table h.val r.2.1 -
    qLearningGreedyTruePolicyValue E table h.val r.2.1 ≤
      table.q (h,(r.2.1,qLearningChronologicalPolicy E table h r.2.1)) -
        qLearningTrueOptimalQ E (h,(r.2.1,qLearningChronologicalPolicy E table h r.2.1)) +
      (onlineMDPSuccessorRowLaw E (h,(r.2.1,qLearningChronologicalPolicy E table h r.2.1))).expectation
        (qLearningGreedyPolicyOptimalityGap E table (h.val+1)) at hstep
  rw [hrow] at hstep
  have hupper := (hgood.2.1 k r).2
  change table.q r - qLearningTrueOptimalQ E r ≤
    onlineQRateWeight H t 0*(H:ℝ) +
    (∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (qLearningChronologicalValue hH E
        (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
        (h.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+h.val) fallback) -
       qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+h.val) fallback))) +
      qLearningSourceBeta H t L cb at hupper
  have hgap : (∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (qLearningChronologicalValue hH E
        (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
        (h.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+h.val) fallback) -
       qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+h.val) fallback))) =
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [hgap] at hupper
  change qLearningChronologicalValue hH E table h.val r.2.1 -
    qLearningGreedyTruePolicyValue E table h.val r.2.1 ≤
      onlineQRateWeight H t 0*(H:ℝ) +
        (∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) +
        qLearningSourceBeta H t L cb +
        qLearningGreedyPolicyOptimalityGap E table (h.val+1) next +
        qLearningGreedyPolicyResidual E table r next
  dsimp only [qLearningGreedyPolicyResidual, r]
  linarith

end StatisticalRL.OnlineRL
