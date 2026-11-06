import Formalization.Online.QLearning.FinBonusBound

/-! Actual Q-error two-sided deterministic consequence of the source noise
event, prior to the optimism induction. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualError_bounds_positive {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (δ cb : ℝ) (hcb : 2 ≤ cb)
    (hL : 0 ≤ Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))
    (path : OnlineOutcomePath.{u,0} State (K*H)) (k : Fin K) (r : OnlineMDPRow State Action H)
    (hgood : qLearningSourceEpisodeNoiseGood hH E fallback
      (fun i => cb*Real.sqrt ((H:ℝ)^3*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)/(i:ℝ))) δ (initial,path))
    (ht : 0 < (qLearningActualVisitEpisodes hH E
      (fun i => cb*Real.sqrt ((H:ℝ)^3*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)/(i:ℝ)))
      initial fallback path k r).length) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    let gap := ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (qLearningChronologicalValue hH E (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
        (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
       qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback))
    let init := onlineQRateWeight H t 0 * ((H:ℝ)-qLearningTrueOptimalQ E r)
    init + gap ≤ (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ∧
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
      init + gap + 4*cb*Real.sqrt ((H:ℝ)^3*L/(t:ℝ)) := by
  classical
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let t := visits.length
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let w : Fin t → ℝ := fun i => onlineQRateWeight H t (i.val+1)
  let next : Fin t → State := fun i => (hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback
  let gap := ∑ i : Fin t, w i * (qLearningChronologicalValue hH E
    (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
    (r.1.val+1) (next i) - qLearningTrueOptimalNext E r (next i))
  let noise := ∑ i : Fin t, w i * (qLearningTrueOptimalNext E r (next i) -
    (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r))
  let B := ∑ i : Fin t, w i * bonus (i.val+1)
  let init := onlineQRateWeight H t 0 * ((H:ℝ)-qLearningTrueOptimalQ E r)
  have he := qLearningActualEpisode_bellmanError hH E bonus initial fallback path k r
  have he' : (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r =
      init+gap+noise+B := by
    dsimp only [init,gap,noise,B,w,next,visits,t,hist,bonus,L] at *
    simp only [mul_add,Finset.sum_add_distrib] at he
    linarith
  have hn := hgood k r ht
  have hn' : |noise| ≤ 2*Real.sqrt ((H:ℝ)^3*L/(t:ℝ)) := by
    change |noise| ≤ 2*Real.sqrt (((H:ℝ)^3/(t:ℝ))*L) at hn
    have he : ((H:ℝ)^3/(t:ℝ))*L = (H:ℝ)^3*L/(t:ℝ) := by ring
    rw [he] at hn
    exact hn
  have hb := qLearning_finBonus_bounds H t hH ht L cb hL hcb
  have hb' : 2*Real.sqrt ((H:ℝ)^3*L/(t:ℝ)) ≤ B ∧
      2*B ≤ 4*cb*Real.sqrt ((H:ℝ)^3*L/(t:ℝ)) := by
    simpa only [B,w,bonus,Nat.cast_add,Nat.cast_one] using hb
  have habs := abs_le.mp (hn'.trans hb'.1)
  change init+gap ≤ _ ∧ _ ≤ init+gap+4*cb*Real.sqrt ((H:ℝ)^3*L/(t:ℝ))
  rw [he']
  constructor <;> linarith [habs.1,habs.2,hb'.2]
end StatisticalRL.OnlineRL
