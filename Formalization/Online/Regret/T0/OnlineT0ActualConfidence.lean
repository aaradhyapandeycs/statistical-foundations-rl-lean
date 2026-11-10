import Formalization.Online.Regret.T0.OnlineT0SingletonSource
import Formalization.Online.Regret.T4.OnlineT4SuffixConfidence
import Formalization.Online.Regret.Algebra.OnlineT56ConfidenceAlgebra

/-! Same-experiment suffix proof component: OnlineT0ActualConfidence.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

noncomputable def onlineActualT0T3SuffixFamily
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample | ∀ j : Fin H,
    (∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
      onlineCappedEpisodeT3 H (onlineT0ActualSuffixStage H K hH E sample.1 fallback sample.2 δ c₁ c₂ k)
        (onlineT0ActualSuffixState H K hH E sample.1 fallback sample.2 δ c₁ c₂ k)
        (onlineT0ActualSuffixAction H K hH E sample.1 fallback sample.2 δ c₁ c₂ k)
        (Real.log (1 / δ)) c₁ c₂ n) ≤
    4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
    4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
    5 * (H : ℝ) * Real.log (1 / δ)}

noncomputable def onlineActualT0T4SuffixFamily
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample | ∀ j : Fin H,
    |∑ k : Fin K, onlineT4SuffixEpisodeIncrement H K hH E fallback
      (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) j.val k sample| ≤
        Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ))}

noncomputable def onlineActualT0OptimisticUniformEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample |
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (K * H) [] sample.2
    onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂ history ∧
      ∀ j : Fin H, (∑ k : Fin K,
        onlineActualStagePolicyGap H K hH E sample.1 fallback sample.2 δ c₁ c₂ j k) ≤
          onlineActualT0SourceUpper H K hH E fallback sample δ c₁ c₂}

/-- Same realized path: W12 already contains optimism, and the two suffix
families supply the only remaining premises of the uniform consumer. -/
theorem onlineT0_optimisticUniform_of_sharedFamilies
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    onlineActualW12SharedHistoryEvent H K hH E fallback δ c₁ c₂ ∩
      (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂ ∩
       onlineActualT0T4SuffixFamily H K hH E fallback δ c₁ c₂) ⊆
    onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂ := by
  intro sample hs
  have hopt := hs.1.2.2
  have hw := onlineW12SharedHistory_implies_suffixIota H K hH hK E fallback δ c₁ c₂
    hδ hδsmall (by linarith) (by nlinarith [sq_nonneg c₁]) hs.1
  exact ⟨hopt, onlineActualStagePolicyGap_uniform_le_sourceT0_of_suffixBounds H K hH hK
    E fallback sample δ c₁ c₂ hδ hδsmall hc₁ hc₂ hw hs.2.1 hs.2.2⟩

/-- For one state, optimism alone implies the same event; no T3 or T4
probability input is required. -/
theorem onlineT0_optimisticUniform_of_singleton [Subsingleton State]
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
      let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
      let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
        (K * H) [] sample.2
      onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂ history} ⊆
    onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂ := by
  intro sample hopt
  exact ⟨hopt, onlineSingleton_actualStageGap_uniform_le_sourceT0 H K hH hK E fallback sample δ c₁ c₂
    hδ hδsmall hc₁ hc₂⟩
noncomputable local instance t0ConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance t0ConfidenceSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

/-- Conditional on the actual masked-T3 family probability. The probability
premise must later be discharged by the same-law T3 family producer. -/
theorem onlineT0_optimisticUniform_confidence_of_T3
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hT3prob :
      let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
      1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ ≤
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
          (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂)) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  by_cases hsingle : Fintype.card State = 1
  · letI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hp := onlineGreedySequential_allStageTrajectoryOptimism_strict H K hH (by omega) E ρ fallback
      δ c₁ c₂ hδ hδsmall hc₁ hc₂
    have hsub := onlineT0_optimisticUniform_of_singleton H K hH hK E fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
    have hm := measureReal_mono (μ := μ) hsub (by simp)
    have hA : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos (α := Action)
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hKr : (0 : ℝ) ≤ K := by positivity
    simp only [OnlineMDPRow, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hp
    change 1 - 9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
      μ.real (onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂)
    have hS1 : (Fintype.card State : ℝ) = 1 := by exact_mod_cast hsingle
    change 1 - 2 * ((H : ℝ) * ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ))) * K * δ < μ.real _ at hp
    simp only [hS1, one_mul, one_pow] at hp ⊢
    have hcoef : 2 * (H : ℝ) ≤ 9 * (H : ℝ)^2 := by nlinarith [sq_nonneg ((H : ℝ) - 1)]
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ (Fintype.card Action : ℝ) * K * δ by positivity)
    nlinarith only [hp, hm, hmul]
  · have hS : 2 ≤ (Fintype.card State : ℝ) := by
      have hs : 2 ≤ Fintype.card State := by have := Fintype.card_pos (α := State); omega
      exact_mod_cast hs
    have hA : 1 ≤ (Fintype.card Action : ℝ) := by exact_mod_cast Fintype.card_pos (α := Action)
    have hHr : 1 ≤ (H : ℝ) := by exact_mod_cast hH
    have hKr : 1 ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
    have hpW := onlineSequential_actualW12_shared_strict H K hH (by omega) E ρ fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
    have hp4 := onlineT4SuffixActualSum_allStages_confidence H K hH (by omega) E ρ fallback planner δ hδ (by linarith)
    have h12 := onlineTwoEvent_confidence_strict μ
      (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂)
      (onlineActualW12SharedHistoryEvent H K hH E fallback δ c₁ c₂)
      (2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ)
      ((4 * (Fintype.card State : ℝ) + 6) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ)
      hT3prob hpW
    have h123 := onlineTwoEvent_confidence_strict μ
      (onlineActualT0T4SuffixFamily H K hH E fallback δ c₁ c₂)
      (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂ ∩
       onlineActualW12SharedHistoryEvent H K hH E fallback δ c₁ c₂)
      (2 * (H : ℝ) * δ)
      (2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ +
        (4 * (Fintype.card State : ℝ) + 6) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ)
      hp4 h12
    have hsub := onlineT0_optimisticUniform_of_sharedFamilies H K hH hK E fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
    have hsub' : onlineActualT0T4SuffixFamily H K hH E fallback δ c₁ c₂ ∩
        (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂ ∩
          onlineActualW12SharedHistoryEvent H K hH E fallback δ c₁ c₂) ⊆
        onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂ := by
      intro x hx
      exact hsub ⟨hx.2.2, hx.2.1, hx.1⟩
    have hm := measureReal_mono (μ := μ) hsub' (by simp)
    have hN : 2 ≤ K * H := by nlinarith
    have hlog := onlineT234_failureCoefficient_le_source (K * H) hN δ (le_of_lt hδ)
    have hfloor : Real.log (K * H) / Real.log 2 ≤ (K : ℝ) * H := by
      simpa only [Nat.cast_mul] using onlineT56_realLog2_le (K * H) (by omega)
    have hcoef := onlineT56_suffix_family_failure_le_nine (Fintype.card State) (Fintype.card Action) H K
      (Real.log (K * H) / Real.log 2) hS hA hHr hKr hfloor
    have hlogH := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (H : ℝ) by positivity)
    have hcoefδ := mul_le_mul_of_nonneg_right hcoef (le_of_lt hδ)
    simp only [OnlineMDPRow, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at h123
    dsimp [planner] at hp4
    simp only [Nat.cast_mul] at hlogH
    change 1 - 9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
      μ.real (onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂)
    nlinarith only [h123, hm, hcoefδ, hlogH]
end StatisticalRL.OnlineRL
