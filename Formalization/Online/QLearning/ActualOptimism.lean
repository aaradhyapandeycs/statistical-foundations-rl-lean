import Formalization.Online.QLearning.ZeroVisitOptimism

/-! Episode induction: actual Q and capped V are optimistic on the proved
source-noise event. The probability of this event is established separately. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualOptimism_on_noise {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 2 ≤ cb)
    (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceEpisodeNoiseGood hH E fallback
      (fun i => cb*Real.sqrt ((H:ℝ)^3*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)/(i:ℝ))) δ (initial,path)) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    ∀ (k : Fin K) (r : OnlineMDPRow State Action H),
      qLearningTrueOptimalQ E r ≤
        (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  have hcard : (1:ℝ) ≤ Fintype.card (OnlineMDPRow State Action H) := by exact_mod_cast Fintype.card_pos
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    rw [one_le_div hδ]
    nlinarith
  have hind : ∀ n : ℕ, ∀ hn : n<K, ∀ r : OnlineMDPRow State Action H,
      qLearningTrueOptimalQ E r ≤
        (qLearningActualTableAt hH E bonus initial fallback path (n*H)).q r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn r
      let k : Fin K := ⟨n,hn⟩
      let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
      let t := visits.length
      by_cases ht : t=0
      · have hz := qLearning_actualZeroVisit_optimistic hH E bonus initial fallback path k r ht
        dsimp [k] at hz
        linarith
      · have htpos : 0<t := by omega
        have he := qLearning_actualError_bounds_positive hH E initial fallback δ cb hcb hL path k r hgood htpos
        let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
        let gap := ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
          (qLearningChronologicalValue hH E
            (qLearningActualTableAt hH E bonus initial fallback path ((visits.get i)*H))
            (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
           qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback))
        have hgap : 0 ≤ gap := by
          dsimp [gap]
          apply Finset.sum_nonneg
          intro i hi
          apply mul_nonneg (onlineQRateWeight_nonneg hH t (i.val+1))
          apply sub_nonneg.mpr
          let e := visits.get i
          let s := (hist.map Prod.snd).getD (e*H+r.1.val) fallback
          have hearlier : e < n := by
            have hm := (qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1
            simpa [e,visits,k] using hm
          have heK : e<K := hearlier.trans hn
          by_cases hnext : r.1.val+1 < H
          · let stage : Fin H := ⟨r.1.val+1,hnext⟩
            have hQ : ∀ a : Action, qLearningTrueOptimalQ E (stage,(s,a)) ≤
                (qLearningActualTableAt hH E bonus initial fallback path (e*H)).q (stage,(s,a)) := by
              intro a
              exact ih e hearlier heK (stage,(s,a))
            have hv := qLearning_value_ge_optimal_of_q hH E
              (qLearningActualTableAt hH E bonus initial fallback path (e*H)) stage s hQ
            simpa [qLearningTrueOptimalNext,stage,e,s,visits,hist] using hv
          · have hlast : r.1.val+1 = H := by have hh := r.1.isLt; omega
            have hz := qLearningTrueOptimalNext_last_zero E r hlast
            simp [qLearningChronologicalValue,hnext,hz,e,s,visits,hist]
        have hinit : 0 ≤ onlineQRateWeight H t 0 * ((H:ℝ)-qLearningTrueOptimalQ E r) :=
          mul_nonneg (onlineQRateWeight_nonneg hH t 0) (sub_nonneg.mpr (qLearningTrueOptimalQ_mem_Icc E r).2)
        dsimp only [L,bonus,visits,t,hist,gap,k] at hgap hinit he ⊢
        linarith [he.1]
  dsimp only
  intro k r
  exact hind k.val k.isLt r
end StatisticalRL.OnlineRL
