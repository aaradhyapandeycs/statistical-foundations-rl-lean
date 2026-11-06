import Formalization.Online.QLearning.ActualOptimismConfidence

/-! Stronger half-budget companions for exactly the same algorithm, logarithm,
noise event and optimism event. The original provider signatures stay intact. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance halfBudgetStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance halfBudgetStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance halfBudgetActionDecidable : DecidableEq Action := Classical.decEq Action
local instance halfBudgetTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance halfBudgetPathMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State n) := ⊤

theorem qLearning_actualStack_rate_union_halfBudget
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (V : OnlineMDPRow State Action H → State → ℝ)
    (hV : ∀ r s, V r s ∈ Set.Icc 0 (H:ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ/2 ≤ (onlineMDPInitialStackLaw E ρ K).real {sample |
      ∀ (r : OnlineMDPRow State Action H) (j : Fin K),
      |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample (V r) (j.val+1) i
          (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*
        Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let μ := onlineMDPInitialStackLaw E ρ K
  letI : IsProbabilityMeasure μ := by dsimp [μ,onlineMDPInitialStackLaw,onlineMDPStackLaw]; infer_instance
  let d : ℝ := Fintype.card (OnlineMDPRow State Action H)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  let ε : ℝ := δ/(2*d*K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hε1 : ε < 1 := by dsimp [ε]; rw [div_lt_one (by positivity)]; nlinarith
  let Good (r : OnlineMDPRow State Action H) (j : Fin K) : Set ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)) := {sample |
    |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample (V r) (j.val+1) i
        (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
    Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*Real.log (2/ε))}
  let I := OnlineMDPRow State Action H × Fin K
  let bad : I → Set _ := fun z => (Good z.1 z.2)ᶜ
  let U : Set _ := ⋃ z,bad z
  have hbad (z : I) : μ.real (bad z) ≤ ε := by
    have h := qLearning_actualStack_rate_confidence H K (z.2.val+1) hH (by omega)
      (Nat.succ_le_of_lt z.2.isLt) E ρ z.1 (V z.1) (hV z.1) ε hε hε1
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (Good z.1 z.2)).measurableSet)
    rw [probReal_univ] at hc
    have hfixed : 1-ε < μ.real (Good z.1 z.2) := by
      simpa only [Good, μ, Nat.cast_add, Nat.cast_one] using h
    dsimp [bad]
    linarith
  have hU : μ.real U ≤ d*K*ε := by
    calc
      _ ≤ ∑ z : I, μ.real (bad z) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _z : I, ε := Finset.sum_le_sum (fun z _ => hbad z)
      _ = d*K*ε := by simp [I,d,Fintype.card_prod]
  have hcomp := measureReal_compl (μ := μ) ((Set.to_countable U).measurableSet)
  rw [probReal_univ] at hcomp
  have hgood : Uᶜ = {sample | ∀ r j, sample ∈ Good r j} := by
    ext sample
    simp [U,bad,I]
  have hlog : 2/ε = 4*d*K/δ := by
    dsimp [ε]
    rw [div_div_eq_mul_div]
    ring
  have hbudget : d*K*ε = δ/2 := by
    dsimp [ε]
    field_simp [ne_of_gt hd,ne_of_gt hk]
  rw [hbudget] at hU
  have hfinal : 1-δ/2 ≤ μ.real Uᶜ := by linarith
  rw [hgood] at hfinal
  simpa [Good, μ, hlog, d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_comm] using hfinal

theorem qLearning_actualOptimalStack_rate_union_halfBudget
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ/2 ≤ (onlineMDPInitialStackLaw E ρ K).real {sample |
      ∀ (r : OnlineMDPRow State Action H) (j : Fin K),
      |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) (j.val+1) i
          (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*
        Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))} := by
  exact qLearning_actualStack_rate_union_halfBudget H K hH hK E ρ
    (qLearningTrueOptimalNext E) (qLearningTrueOptimalNext_mem_Icc E) δ hδ hδ1

theorem qLearning_actualObservedOptimalNoise_confidence_halfBudget
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (bonus : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ/2 ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback
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
  have hgood : 1-δ/2 ≤ μ.real good :=
    qLearning_actualOptimalStack_rate_union_halfBudget H K hH hK E ρ δ hδ hδ1
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
  change 1-δ/2 ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback
    (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample | (sample.1,qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2) ∈ target}
  rw [← heq]
  exact hgood.trans hmono

theorem qLearning_sourceEpisodeNoise_confidence_halfBudget
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (bonus : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ/2 ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback
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
  have hgood : 1-δ/2 ≤ μ.real good :=
    qLearning_actualObservedOptimalNoise_confidence_halfBudget H K hH hK E ρ fallback bonus δ hδ hδ1
  have hsub : good ⊆ target := by
    intro sample hs
    change qLearningSourceEpisodeNoiseGood hH E fallback bonus δ sample
    unfold qLearningSourceEpisodeNoiseGood
    intro k r
    dsimp only
    intro ht
    exact qLearning_actualEpisode_sourceNoise hH E bonus sample.1 fallback sample.2 k r δ hδ hδ1.le hs ht
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  exact hgood.trans hmono

theorem qLearning_sourceOptimism_confidence_halfBudget
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ cb : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hcb : 2 ≤ cb) :
    let L := Real.log ((Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ)
    let bonus := fun i : ℕ => cb*Real.sqrt ((H:ℝ)^3*L/(i:ℝ))
    1-δ/2 ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback
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
  have hgood : 1-δ/2 ≤ μ.real good :=
    qLearning_sourceEpisodeNoise_confidence_halfBudget H K hH hK E ρ fallback bonus δ hδ hδ1
  have hsub : good ⊆ target := by
    intro sample hs
    exact qLearning_sourceOptimismGood_of_noise hH hK E sample.1 fallback δ cb hδ hδ1 hcb sample.2 hs
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  exact hgood.trans hmono

end StatisticalRL.OnlineRL
