import Formalization.Online.QLearning.ActualOptimism

/-! Source Q error sandwich on the actual simultaneous noise event. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

noncomputable def qLearningSourceBeta (H t : ℕ) (L cb : ℝ) : ℝ :=
  if t=0 then 0 else 4*cb*Real.sqrt ((H:ℝ)^3*L/(t:ℝ))

theorem qLearning_actualError_all_on_noise {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 2 ≤ cb)
    (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceEpisodeNoiseGood hH E fallback
      (fun i => cb*Real.sqrt ((H:ℝ)^3*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)/(i:ℝ))) δ (initial,path)) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    ∀ (k : Fin K) (r : OnlineMDPRow State Action H),
      let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
      let t := visits.length
      let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
      let gap := ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
        (qLearningChronologicalValue hH E (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
          (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
         qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback))
      0 ≤ (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ∧
      (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
        onlineQRateWeight H t 0 * (H:ℝ) + gap + qLearningSourceBeta H t L cb := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  have hcard : (1:ℝ) ≤ Fintype.card (OnlineMDPRow State Action H) := by exact_mod_cast Fintype.card_pos
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hL : 0 ≤ L := by dsimp [L]; apply Real.log_nonneg; rw [one_le_div hδ]; nlinarith
  have hopt := qLearning_actualOptimism_on_noise hH hK E initial fallback δ cb hδ hδ1 hcb path hgood
  dsimp only at hopt ⊢
  intro k r
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let t := visits.length
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let gap := ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
    (qLearningChronologicalValue hH E (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
      (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
     qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback))
  have hlo := hopt k r
  constructor
  · linarith
  · by_cases ht : t=0
    · have hzero := qLearning_actualZeroVisit_q hH E bonus initial fallback path k r ht
      have hq := (qLearningTrueOptimalQ_mem_Icc E r).1
      have hz : gap=0 := by
        dsimp only [gap]
        apply Finset.sum_eq_zero
        intro i hi
        have : i.val < 0 := by simpa [t,visits,ht] using i.isLt
        omega
      have hw : onlineQRateWeight H t 0=1 := by rw [qLearning_rate_zero_eq hH,if_pos ht]
      change (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
        onlineQRateWeight H t 0 * (H:ℝ) + gap + qLearningSourceBeta H t L cb
      rw [hzero,hw,hz]
      simp [qLearningSourceBeta,ht]
      linarith
    · have htpos : 0<t := by omega
      have he := qLearning_actualError_bounds_positive hH E initial fallback δ cb hcb hL path k r hgood htpos
      have hq := (qLearningTrueOptimalQ_mem_Icc E r).1
      have hw := onlineQRateWeight_nonneg hH t 0
      change (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
        onlineQRateWeight H t 0 * (H:ℝ) + gap + qLearningSourceBeta H t L cb
      have heupper := he.2
      change (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
        onlineQRateWeight H t 0 * ((H:ℝ)-qLearningTrueOptimalQ E r) + gap +
          4*cb*Real.sqrt ((H:ℝ)^3*L/(t:ℝ)) at heupper
      simp only [qLearningSourceBeta,if_neg ht]
      nlinarith [mul_nonneg hw hq]
end StatisticalRL.OnlineRL
