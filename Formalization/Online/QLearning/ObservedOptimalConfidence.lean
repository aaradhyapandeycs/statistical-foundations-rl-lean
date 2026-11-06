import Formalization.Online.QLearning.ObservedRowPrefix
import Formalization.Online.QLearning.OptimalStackUnion

/-! Optimal-value weighted noise on the actual sequential transcript, for
all deterministic prefixes that actually occurred. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningNoiseStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance qLearningNoiseStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance qLearningNoiseActionDecidable : DecidableEq Action := Classical.decEq Action
local instance qLearningNoiseTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance qLearningNoisePathMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def qLearningObservedOptimalNoiseGood {H K : ℕ}
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (δ : ℝ)
    (record : OnlineResetTranscript State Action H K) : Prop :=
  ∀ (r : OnlineMDPRow State Action H) (j : Fin K),
    j.val+1 ≤ (onlineRowOutcomes record.2 r).length →
    |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) (j.val+1) i
        (fun x => (onlineRowOutcomes record.2 r).getD x.val fallback)| ≤
    Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*
      Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))

theorem qLearning_actualObservedOptimalNoise_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (bonus : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample | qLearningObservedOptimalNoiseGood E fallback δ
        (sample.1,qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2)} := by
  classical
  let μ := onlineMDPInitialStackLaw E ρ K
  letI : IsProbabilityMeasure μ := by dsimp [μ,onlineMDPInitialStackLaw,onlineMDPStackLaw]; infer_instance
  let good := {sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) |
    ∀ (r : OnlineMDPRow State Action H) (j : Fin K),
      |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) (j.val+1) i
          (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*
        Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))}
  let target : Set (OnlineResetTranscript State Action H K) :=
    {record | qLearningObservedOptimalNoiseGood E fallback δ record}
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1,onlineStackHistory
      (onlineEpisodicChoose H K hH sample.1 fallback (qLearningActualEpisodePlanner hH E bonus))
      (onlineFiniteStackExtend K fallback sample.2) (K*H))
  have hgood : 1-δ < μ.real good :=
    qLearning_actualOptimalStack_rate_union H K hH hK E ρ δ hδ hδ1
  have hsub : good ⊆ observe ⁻¹' target := by
    intro sample hs
    change qLearningObservedOptimalNoiseGood E fallback δ (observe sample)
    intro r j hj
    have hp := qLearning_observedPrefix_eq_stack hH E bonus sample.1 fallback sample.2
      (K*H) le_rfl r (j.val+1) hj
    change (fun i : Fin (j.val+1) => (onlineRowOutcomes
      (onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback
        (qLearningActualEpisodePlanner hH E bonus))
        (onlineFiniteStackExtend K fallback sample.2) (K*H)) r).getD i.val fallback) = _ at hp
    rw [hp]
    exact hs r j
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have heq := qLearning_stack_sequential_transcriptEvent_real_eq H K hH E ρ fallback bonus target
  change 1-δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback
    (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample | (sample.1,qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2) ∈ target}
  rw [← heq]
  exact lt_of_lt_of_le hgood hmono
end StatisticalRL.OnlineRL
