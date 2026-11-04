import Formalization.Online.Regret.Joint.T234Definitions
import Formalization.Online.Regret.T2.OnlineT2SourceBound
import Formalization.Online.Regret.T4.OnlineRegretT4SourceConfidence
import Formalization.Online.Regret.T3.OnlineRegretT3SourceEvent
import Formalization.Probability.OnlineT234ConfidenceAlgebra

/-! Joint source T2/T3/T4 bounds on one actual sequential experiment.
Source: onlineRL.tex 988–1005, lem:bound-T234. The algorithm uses the explicit
finite zero-count completion and one fixed greedy tie; K ≥ 2 is explicit. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t234JointStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t234JointSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

theorem onlineSourceAllocated_actualT234_K2_strict
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ I : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hI : 8 * max (c₁^2) c₂ * (Real.log K / Real.log 2) *
      Real.log (1 / onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K) ≤ I) :
    let δ' := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 4 * (Real.log ((K : ℝ) * H) / Real.log 2) * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT234SourceEvent H K hH E fallback δ' c₁ c₂ I) := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ
    (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let L₂ := Real.log ((K : ℝ) * H) / Real.log 2
  let good3 := onlineActualT3SourceBoundEvent H K hH E fallback δ' c₁ c₂
  let good4 : Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    {sample |
      |∑ k : Fin K,
        (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.2| ≤
        Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ'))}
  have hKpos : 0 < K := by omega
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hKpos
  have hδpos : 0 < δ' := hd.1
  have hδsmall : δ' ≤ 1 / 100 := hd.2
  have h3 : 1 - 2 * L₂ * δ' ≤ μ.real good3 :=
    onlineSourceAllocated_actualT3_bound H K hH hK E ρ fallback δ c₁ c₂
      hδ hδone (by linarith) (by nlinarith [sq_nonneg c₁])
  have h4 : 1 - 2 * δ' < μ.real good4 :=
    onlineActualT4_source_confidence_strict H K hH hKpos E ρ fallback δ' c₁ c₂
      hδpos (by linarith)
  have hinter := onlineTwoEvent_confidence_strict μ good3 good4
    (2 * L₂ * δ') (2 * δ') h3 h4
  have hsub : good3 ∩ good4 ⊆ onlineActualT234SourceEvent H K hH E fallback δ' c₁ c₂ I := by
    intro sample hs
    have h2 := onlineActualT2_le_sourceBound H K hH hK E sample.1 fallback sample.2
      δ' c₁ c₂ I hδpos hδsmall hc₁ hc₂ hI
    exact ⟨h2, hs.1, hs.2⟩
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hlogone : 1 ≤ L₂ := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hKH : (2 : ℝ) ≤ (K : ℝ) * H := by
      exact_mod_cast hK.trans (Nat.le_mul_of_pos_right K hH)
    simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2) hKH
  have hmargin : 1 - 4 * L₂ * δ' ≤ 1 - (2 * L₂ * δ' + 2 * δ') := by
    have hh := mul_nonneg (sub_nonneg.mpr hlogone) hδpos.le
    nlinarith
  exact hmargin.trans_lt (hinter.trans_le hmono)

end StatisticalRL.OnlineRL
