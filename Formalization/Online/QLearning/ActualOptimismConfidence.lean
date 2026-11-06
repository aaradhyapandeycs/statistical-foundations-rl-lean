import Formalization.Online.QLearning.ActualErrorAll

/-! Simultaneous actual Q-error and capped-V optimism on the source noise
experiment. A source-facing index and independent statement review remain. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance qLearningOptimismConfidenceStateMeasurable : MeasurableSpace State := ⊤
local instance qLearningOptimismConfidencePathMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State n) := ⊤
attribute [local instance] Classical.propDecidable

noncomputable def qLearningSourceOptimismGood {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (δ cb : ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : Prop :=
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  (qLearningSourceBeta H 0 L cb = 0 ∧
    ∀ t : ℕ, 0 < t → qLearningSourceBeta H t L cb ≤ 4*cb*Real.sqrt ((H:ℝ)^3*L/(t:ℝ))) ∧
  (∀ (k : Fin K) (r : OnlineMDPRow State Action H),
    let visits := qLearningActualVisitEpisodes hH E bonus sample.1 fallback sample.2 k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2
    let gap := ∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      (qLearningChronologicalValue hH E (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 ((visits.get i)*H))
        (r.1.val+1) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
       qLearningTrueOptimalNext E r ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback))
    0 ≤ (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)).q r - qLearningTrueOptimalQ E r ∧
    (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)).q r - qLearningTrueOptimalQ E r ≤
      onlineQRateWeight H t 0 * (H:ℝ) + gap + qLearningSourceBeta H t L cb) ∧
  (∀ (k : Fin K) (h : Fin H) (s : State),
    EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      qLearningChronologicalValue hH E (qLearningActualTableAt hH E bonus sample.1 fallback sample.2 (k.val*H)) h.val s)

theorem qLearning_sourceOptimismGood_of_noise {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State) (fallback : State)
    (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 2 ≤ cb)
    (path : OnlineOutcomePath.{u,0} State (K*H))
    (hgood : qLearningSourceEpisodeNoiseGood hH E fallback
      (fun i => cb*Real.sqrt ((H:ℝ)^3*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)/(i:ℝ))) δ (initial,path)) :
    qLearningSourceOptimismGood hH E fallback δ cb (initial,path) := by
  classical
  dsimp only [qLearningSourceOptimismGood]
  constructor
  · constructor
    · simp [qLearningSourceBeta]
    · intro t ht
      simp [qLearningSourceBeta,ne_of_gt ht]
  constructor
  · exact qLearning_actualError_all_on_noise hH hK E initial fallback δ cb hδ hδ1 hcb path hgood
  · intro k h s
    apply qLearning_value_ge_optimal_of_q hH E _ h s
    intro a
    exact qLearning_actualOptimism_on_noise hH hK E initial fallback δ cb hδ hδ1 hcb path hgood k (h,(s,a))

/-- Actual sequential-law Q/V optimism and weighted error upper bound hold
simultaneously with strict probability above 1−δ. -/
theorem qLearning_sourceOptimism_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 2 ≤ cb) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    1-δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample | qLearningSourceOptimismGood hH E fallback δ cb sample} := by
  classical
  dsimp only
  let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
  let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  let good := {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
    qLearningSourceEpisodeNoiseGood hH E fallback bonus δ sample}
  let target := {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
    qLearningSourceOptimismGood hH E fallback δ cb sample}
  have hgood : 1-δ < μ.real good :=
    qLearning_sourceEpisodeNoise_confidence H K hH hK E ρ fallback bonus δ hδ hδ1
  have hsub : good ⊆ target := by
    intro sample hs
    exact qLearning_sourceOptimismGood_of_noise hH hK E sample.1 fallback δ cb hδ hδ1 hcb sample.2 hs
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  exact lt_of_lt_of_le hgood hmono
end StatisticalRL.OnlineRL
