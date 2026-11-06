import Formalization.Online.QLearning.ActualPolicyGapRange

/-! Source horizon recursion before bounding initialization/bonus charges.
All summands below are the actual sequential algorithm's own path quantities. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actual_stage_recursion {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceOptimismGood hH E fallback δ cb (initial,path)) (h : Fin H) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
    let table := fun k : Fin K => qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
    let visits := fun k : Fin K => qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    let next := fun k : Fin K => (hist.map Prod.snd).getD (k.val*H+h.val) fallback
    (∑ k : Fin K, (qLearningChronologicalValue hH E (table k) h.val (rows k.val).1 -
      qLearningGreedyTruePolicyValue E (table k) h.val (rows k.val).1)) ≤
      (∑ k : Fin K, onlineQRateWeight H (visits k).length 0*(H:ℝ)) +
      (1+1/(H:ℝ))*(∑ k : Fin K,
        (qLearningChronologicalValue hH E (table k) (h.val+1) (next k) -
          qLearningGreedyTruePolicyValue E (table k) (h.val+1) (next k))) +
      (∑ k : Fin K, qLearningSourceBeta H (visits k).length L cb) +
      (∑ k : Fin K, qLearningGreedyPolicyResidual E (table k) (h,rows k.val) (next k)) := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let rows := qLearningActualStageRowSequence hH E bonus initial fallback path h
  let table := fun k : Fin K => qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
  let visits := fun k : Fin K => qLearningActualVisitEpisodes hH E bonus initial fallback path k (h,rows k.val)
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let next := fun k : Fin K => (hist.map Prod.snd).getD (k.val*H+h.val) fallback
  let gap := qLearningActualStageGap hH E bonus initial fallback path h
  let prop := fun k : Fin K => ∑ i : Fin (visits k).length,
    onlineQRateWeight H (visits k).length (i.val+1)*gap ((visits k).get i)
  let init := fun k : Fin K => onlineQRateWeight H (visits k).length 0*(H:ℝ)
  let beta := fun k : Fin K => qLearningSourceBeta H (visits k).length L cb
  let policyGap := fun k : Fin K => qLearningGreedyPolicyOptimalityGap E (table k) (h.val+1) (next k)
  let residual := fun k : Fin K => qLearningGreedyPolicyResidual E (table k) (h,rows k.val) (next k)
  let current := fun k : Fin K => qLearningChronologicalValue hH E (table k) h.val (rows k.val).1 -
    qLearningGreedyTruePolicyValue E (table k) h.val (rows k.val).1
  let future := fun k : Fin K => qLearningChronologicalValue hH E (table k) (h.val+1) (next k) -
    qLearningGreedyTruePolicyValue E (table k) (h.val+1) (next k)
  let c : ℝ := 1+1/(H:ℝ)
  have hstep (k : Fin K) : current k ≤ init k + prop k + beta k + policyGap k + residual k :=
    qLearning_actual_regret_oneStep hH E initial fallback δ cb path hgood h k
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hstep k)
  simp only [Finset.sum_add_distrib] at hsum
  have hprop : (∑ k : Fin K, prop k) ≤ c*(∑ k : Fin K, gap k.val) :=
    qLearning_actualStageGap_propagation hH E initial fallback δ cb path hgood h
  have hcombine (k : Fin K) : c*gap k.val + policyGap k ≤ c*future k := by
    have hp : 0 ≤ policyGap k :=
      (qLearning_greedyPolicyOptimalityGap_mem_Icc hH E (table k) (h.val+1) (next k)).1
    have hcoef : 0 ≤ 1/(H:ℝ) := by positivity
    have heq : gap k.val + policyGap k = future k := by
      dsimp only [gap,qLearningActualStageGap,policyGap,qLearningGreedyPolicyOptimalityGap,
        future,next,table,hist,rows,qLearningTrueOptimalNext]
      ring
    dsimp only [c]
    nlinarith
  have hcomb := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hcombine k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hcomb
  change (∑ k : Fin K, current k) ≤ (∑ k : Fin K, init k) +
    c*(∑ k : Fin K, future k) + (∑ k : Fin K, beta k) + (∑ k : Fin K, residual k)
  linarith

end StatisticalRL.OnlineRL
