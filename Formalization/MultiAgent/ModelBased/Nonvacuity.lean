import Formalization.MultiAgent.ModelBased.Planner
import Formalization.MultiAgent.ModelBased.Restricted

/-!
# Theorem 7.6 (restricted), clause (a) instantiated with a Lean-constructed causal CCE oracle

`thm7_6_restricted_ccePlanner`: the backward-induction planner `ccePlanner hA` (stage-CCE
existence via `geometric_hahn_banach_compact_closed`, no Nash theorem) meets the hypotheses of
clause (a), so the CCE clause is non-vacuous. (A causal NE oracle for general-sum games needs Nash's
theorem, which is not in Mathlib; clause (b) is proved for every causal NE oracle.)
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

theorem thm7_6_restricted_ccePlanner :
    ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (m S H : ℕ) (A : Fin m → ℕ) (hS : 0 < S) (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A),
      (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) →
    ∀ (N : ℕ) (hN : 0 < N) (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ Real.sqrt H →
      C₁ * (H : ℝ) ^ 3 / ε ^ 2 *
          Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gapJ G (ccePlanner hA (empiricalGame G N hN data)) ≤ ε} := by
  obtain ⟨C₁, hC₁, h⟩ := thm7_6_restricted
  refine ⟨C₁, hC₁, ?_⟩
  intro m S H A hS hA G hR N hN δ ε hδ hδ1 hε hεH hthr
  exact (h m S H A hS hA G hR N hN δ ε hδ hδ1 hε hεH hthr).1 (ccePlanner hA) (ccePlanner_causal hA)
    (fun data => ccePlanner_isCCE hA _)

end StatisticalRL.Ch7Rest.Marl76
