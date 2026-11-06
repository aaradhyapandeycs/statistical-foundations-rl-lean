import Formalization.Online.QLearning.EpisodeSourceNoiseAll

/-! Unconditional actual sequential-law probability for the source-shaped
ordered-episode noise term. This is not the full optimism/error induction. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningSourceNoiseStateMeasurable : MeasurableSpace State := ⊤
local instance qLearningSourceNoisePathMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def qLearningSourceEpisodeNoiseGood {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (bonus : ℕ → ℝ) (δ : ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath State (K*H)) : Prop :=
  ∀ (k : Fin K) (r : OnlineMDPRow State Action H),
    let visits := qLearningActualVisitEpisodes hH E bonus sample.1 fallback sample.2 k r
    let t := visits.length
    let hist := qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2
    0 < t →
    |∑ i : Fin t, onlineQRateWeight H t (i.val+1) *
      ((qLearningTrueOptimalNext E r) ((hist.map Prod.snd).getD ((visits.get i)*H+r.1.val) fallback) -
        (onlineMDPSuccessorRowLaw E r).expectation (qLearningTrueOptimalNext E r))| ≤
    2*Real.sqrt ((H:ℝ)^3/(t:ℝ)*Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))

/-- The actual source-shaped ordered-episode optimal-value noise bounds hold
simultaneously with strict probability above 1−δ. -/
theorem qLearning_sourceEpisodeNoise_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (bonus : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample | qLearningSourceEpisodeNoiseGood hH E fallback bonus δ sample} := by
  classical
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  let good := {sample : (Fin K → State) × OnlineOutcomePath State (K*H) |
    qLearningObservedOptimalNoiseGood E fallback δ
      (sample.1,qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2)}
  let target := {sample : (Fin K → State) × OnlineOutcomePath State (K*H) |
    qLearningSourceEpisodeNoiseGood hH E fallback bonus δ sample}
  have hgood : 1-δ < μ.real good :=
    qLearning_actualObservedOptimalNoise_confidence H K hH hK E ρ fallback bonus δ hδ hδ1
  have hsub : good ⊆ target := by
    intro sample hs
    change qLearningSourceEpisodeNoiseGood hH E fallback bonus δ sample
    unfold qLearningSourceEpisodeNoiseGood
    intro k r
    dsimp only
    intro ht
    exact qLearning_actualEpisode_sourceNoise hH E bonus sample.1 fallback sample.2 k r δ hδ hδ1.le hs ht
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  exact lt_of_lt_of_le hgood hmono
end StatisticalRL.OnlineRL
