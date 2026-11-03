import Formalization.Generative.FiniteHorizonOneStage

/-! Source-shaped positive-episode sample guarantee for the concrete causal
empirical backward planner, with a fully explicit universal constant. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance finiteMainStateMeasurable : MeasurableSpace State := ⊤

/-- The source sample threshold, retaining the specified causal local greedy
planner and actual simultaneous all-stage V/forced-action-Q event. -/
theorem mainSample_causalFinitePolicy {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεH : ε ≤ H)
    (hsize : 8640 * (H : ℝ) ^ 3 *
      Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N) :
    1 - δ ≤ (samplingLaw E N).real {data | CausalPolicyPerformanceEvent E N hN fallback ε data} := by
  by_cases hδ1 : δ < 1
  · by_cases hH1 : H = 1
    · subst H
      have he : {data : Samples State Action 1 N | CausalPolicyPerformanceEvent E N hN fallback ε data} = Set.univ := by
        ext data
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact causalPolicyPerformanceEvent_mono E N hN fallback 0 ε hε.le data
          (oneStage_causalPolicyPerformance E N hN fallback data)
      rw [he, probReal_univ]
      linarith
    · have hH2 : 2 ≤ H := by omega
      have hrow : (Fintype.card (Fin H × State × Action) : ℝ) =
          (H : ℝ) * Fintype.card State * Fintype.card Action := by
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        ring
      have hcal := auxiliary_sample_threshold_arithmetic (H : ℝ) (N : ℝ) ε
        (allLevelBeta (H := H) State Action δ)
        (Real.log ((Fintype.card (Fin H × State × Action) : ℝ) / δ))
        (Nat.cast_pos.mpr hH) (Nat.cast_pos.mpr hN) hε hεH
        (allLevelBeta_pos E hH δ hδ hδ1)
        (allLevelBeta_le_source_log E hH2 δ hδ hδ1) (by simpa only [hrow] using hsize)
      have hp := causalPolicyPerformance_probability E N hN hH fallback δ hδ hδ1 hcal.1
      apply hp.le.trans
      apply measureReal_mono _ (measure_ne_top (samplingLaw E N) _)
      intro data hd
      exact causalPolicyPerformanceEvent_mono E N hN fallback _ ε hcal.2 data hd
  · have hp : 0 ≤ (samplingLaw E N).real {data | CausalPolicyPerformanceEvent E N hN fallback ε data} :=
      measureReal_nonneg
    linarith

/-- A single numerical constant precedes all finite carriers, models, horizons,
confidence/accuracy parameters and sample sizes, as in Thm:sample-compl-finite. -/
theorem exists_universal_causalFinitePolicy_sample_constant :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (State Action : Type*) [Fintype State] [Fintype Action]
        (H : ℕ) (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
        (_hH : 0 < H) (fallback : Action) (δ ε : ℝ),
        0 < δ → 0 < ε → ε ≤ H →
        c₀ * (H : ℝ) ^ 3 *
          Real.log ((H : ℝ) * Fintype.card State * Fintype.card Action / δ) / ε ^ 2 ≤ N →
        1 - δ ≤ (samplingLaw E N).real {data | CausalPolicyPerformanceEvent E N hN fallback ε data} := by
  refine ⟨8640, by norm_num, ?_⟩
  intro State Action _ _ H E N hN hH fallback δ ε hδ hε hεH hsize
  exact mainSample_causalFinitePolicy E N hN hH fallback δ ε hδ hε hεH hsize

end StatisticalRL.FiniteHorizonGenerative
