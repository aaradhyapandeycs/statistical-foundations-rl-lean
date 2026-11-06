import Formalization.Online.QLearning.SourceRadiusAbsorption
import Formalization.Online.QLearning.EpisodeIndexedNoise

/-! Source-log comparison for actual ordered episode noise when H≥2. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualEpisode_sourceNoise_nonterminal {H K : ℕ} (hH : 0 < H)
    (hH2 : 2 ≤ H) (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgood : qLearningObservedOptimalNoiseGood E fallback δ
      (initial,qLearningActualSequentialHistory hH E bonus initial fallback path))
    (ht : 0 < (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      ((qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
        (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r))| ≤
    2*Real.sqrt ((H:ℝ)^3/(t:ℝ)*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)) := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hs : 1 ≤ Fintype.card State := Fintype.card_pos
  have ha : 1 ≤ Fintype.card Action := Fintype.card_pos
  have hk : 1 ≤ K := by have h := k.isLt; omega
  have hxnat : 2 ≤ Fintype.card (OnlineMDPRow State Action H)*K := by
    simp only [OnlineMDPRow, Fintype.card_prod, Fintype.card_fin]
    have hp : 1 ≤ (Fintype.card State * Fintype.card Action) * K := by
      have hp0 : 0 < (Fintype.card State * Fintype.card Action) * K :=
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
      omega
    have hm := Nat.mul_le_mul_left H hp
    simp only [Nat.mul_one] at hm
    rw [Nat.mul_assoc]
    exact hH2.trans hm
  have hx : (2:ℝ) ≤ (Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ) := by exact_mod_cast hxnat
  let t := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length
  have hA : (0:ℝ) ≤ (H:ℝ)^3/(t:ℝ) := by positivity
  have hbound := qLearning_actualEpisodeIndexed_noise_bound hH E bonus initial fallback path k r δ hgood ht
  have habsorb := qLearning_source_radius_absorb ((H:ℝ)^3/(t:ℝ))
    ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)) δ hA hx hδ hδ1
  exact hbound.trans (by simpa [mul_assoc] using habsorb)
end StatisticalRL.OnlineRL
