import Formalization.Online.SourceOptimism.ObservedPrefixEvent

/-! Actual direct sequential observed-prefix
certificate probability, obtained by inclusion and full law comparison, never
by treating the counterfactual all-prefix event as history-measurable. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineObservedProbabilityStateMeasurable : MeasurableSpace State := ⊤
local instance onlineObservedProbabilityTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance onlineObservedProbabilityAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤
noncomputable local instance onlineObservedProbabilityStateDecidableEq : DecidableEq State := Classical.decEq State
noncomputable local instance onlineObservedProbabilityActionDecidableEq : DecidableEq Action := Classical.decEq Action

/-- Fixed true-V row certificates hold at all actual pre-episode empirical
counts under the direct sequential source experiment with the printed factor2.
This is still a certificate theorem, not the final backward-optimism lemma. -/
theorem onlineSequential_observedPrefixCertificates_strict
    (H K : ℕ) (hH : 0<H) (hK : 0<K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (V : OnlineMDPRow State Action H → State → ℝ) (δ c₁ c₂ : ℝ)
    (hδ : 0<δ) (hδsmall : δ≤2/5) (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂)
    (hV : ∀ r s,V r s∈Set.Icc 0 (H : ℝ)) :
    1-2*(Fintype.card (OnlineMDPRow State Action H) : ℝ)*K*δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample | onlineObservedPrefixBonusCertificates H K E V δ c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K*H) [] sample.2)} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let μ := onlineMDPInitialStackLaw E ρ K
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, onlineMDPInitialStackLaw, onlineMDPStackLaw]
    infer_instance
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)
  let good := {data | ∀ r n,3≤n → n<K →
    data∈onlineStackPrefixBonusGood (onlineMDPSuccessorRowLaw E) V K
      (H : ℝ) δ c₁ c₂ r n}
  let target : Set (OnlineResetTranscript State Action H K) :=
    {record | onlineObservedPrefixBonusCertificates H K E V δ c₁ c₂ record.2}
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1,onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (onlineFiniteStackExtend K fallback sample.2) (K*H))
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State (K*H) =>
    (sample.1,onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2)
  have hstack := onlineStack_allPrefixes_sourceBonus_strict (onlineMDPSuccessorRowLaw E) V
    K hK (H : ℝ) δ c₁ c₂ (by exact_mod_cast hH) hδ hδsmall hc₁ hc₂ hV
  have hlift : μ.real (Set.univ ×ˢ good)=
      (onlineMDPStackLaw E K).real good := by
    dsimp [μ,onlineMDPInitialStackLaw]
    rw [measureReal_def,Measure.prod_prod,measure_univ,one_mul]
    rfl
  have hsub : (Set.univ ×ˢ good) ⊆ observe ⁻¹' target := by
    intro sample hgood
    exact onlineStack_allPrefixGood_implies_observedCertificates H K hH E
      sample.1 fallback planner V δ c₁ c₂ sample.2 hgood.2
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hcouple : μ.map observe=ν.rowMeasure.map encode :=
    onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner (K*H) le_rfl
  have hprob : μ.real (observe ⁻¹' target)=ν.rowMeasure.real (encode ⁻¹' target) := by
    have h := congrArg (fun law : Measure (OnlineResetTranscript State Action H K) =>
      law.real target) hcouple
    simpa only [measureReal_def,Measure.map_apply (measurable_of_countable _)
      ((Set.to_countable target).measurableSet)] using h
  change 1-2*(Fintype.card (OnlineMDPRow State Action H) : ℝ)*K*δ <
    ν.rowMeasure.real (encode ⁻¹' target)
  rw [← hprob]
  apply lt_of_lt_of_le _ (hlift.symm.le.trans hmono)
  simpa [good, onlineMDPStackLaw] using hstack

end StatisticalRL.OnlineRL
