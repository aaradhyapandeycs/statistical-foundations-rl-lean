import Formalization.Online.SourceOptimism.CappedGreedyPlannerCorrespondence
import Formalization.Online.SourceOptimism.ObservedPrefixProbability

/-! The SAME causal greedy planner is inserted into
the actual sequential experiment and deterministic same-history certificate
consumption. Source delta-prime allocation and actual optimal-trajectory
identification remain separate obligations, not new assumed conclusions. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineGreedyBellmanStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- All played episodes and active stages, evaluated on one actual full history.
Source stage h_source is zero-based h_source−1; only completed earlier episodes
feed its table. These are true Bellman optima, pending the trajectory adapter. -/
def onlineHistoryAllStageBellmanOptimism
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (δ c₁ c₂ : ℝ) (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ h : Fin H,
    (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val s) ∧
    (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
      onlineCappedBackwardQAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val s a)

/-- The fixed true row family satisfies the Bernstein range without any
empirical continuation, random policy, or target optimism premise. -/
theorem onlineTrueSuffixRowFamily_range
    (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (r : OnlineMDPRow State Action H) (s : State) :
    onlineTrueSuffixRowFamily E r s ∈ Set.Icc 0 (H : ℝ) := by
  have hb := onlineTrueOptimalValue_range_length ((List.ofFn E).drop (r.1.val + 1)) s
  have hlen : ((List.ofFn E).drop (r.1.val + 1)).length ≤ H := by
    simp only [List.length_drop, List.length_ofFn]
    omega
  have hlenR : (((List.ofFn E).drop (r.1.val + 1)).length : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast hlen
  exact ⟨hb.1, hb.2.trans hlenR⟩

/-- Strict factor-2 confidence on the actual direct sequential law, instantiated
with the very same fixed greedy planner used to construct the capped tables.
Only source small-confidence domain is explicit here; the source delta-prime
formula and cardinality simplification remain to be derived later. -/
theorem onlineGreedySequential_allStageBellmanOptimism_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 2 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample | onlineHistoryAllStageBellmanOptimism H K E δ c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K * H) [] sample.2)} := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  let observe := fun sample : (Fin K → State) × OnlineOutcomePath State (K * H) =>
    onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  have hsmall : δ ≤ 2 / 5 := by linarith
  have hprob := onlineSequential_observedPrefixCertificates_strict H K hH hK E ρ
    fallback planner (onlineTrueSuffixRowFamily E) δ c₁ c₂ hδ hsmall hc₁ hc₂
    (onlineTrueSuffixRowFamily_range H E)
  have hL : 1 ≤ Real.log (1 / δ) := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hsub :
      {sample | onlineObservedPrefixBonusCertificates H K E
        (onlineTrueSuffixRowFamily E) δ c₁ c₂ (observe sample)} ⊆
      {sample | onlineHistoryAllStageBellmanOptimism H K E δ c₁ c₂ (observe sample)} := by
    intro sample hs k h
    exact onlineObservedCertificates_imply_allStageBellmanOptimism H K E
      (observe sample) δ c₁ c₂ hL hc₁ hc₂ hs k h
  have hmono := measureReal_mono hsub (measure_ne_top ν.rowMeasure _)
  change 1 - 2 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
    ν.rowMeasure.real {sample | onlineHistoryAllStageBellmanOptimism H K E δ c₁ c₂
      (observe sample)}
  exact hprob.trans_le hmono

end StatisticalRL.OnlineRL
