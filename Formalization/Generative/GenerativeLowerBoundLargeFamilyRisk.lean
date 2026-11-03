import Formalization.Generative.GenerativeLowerBoundFanoThreshold
import Formalization.Generative.GenerativeLowerBoundFamilyDecision

/-! Corrected large-family policy-risk consequence. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance largeRiskStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance largeRiskFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- A common policy estimator has strict >0.1 risk on an actual indexed MDP,
under an explicit quarter-log budget and the source-size K≥4 regime. -/
theorem sourceFamily_large_policy_risk {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsize : 16 ≤ (m + 1) * (n + 1))
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 4096 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤
      Real.log (Fintype.card (HardFamilyIndex m n)))
    (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N → Option (Fin m) → Fin (n + 1)) :
    ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 10 < (samplingLaw M N).real {data | ε < ‖M.trajectoryExpectedQ
        (deterministicFamilyPolicy (estimate data)) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  have hk : (4 : ℝ) ≤ Fintype.card (HardFamilyIndex m n) := by
    exact_mod_cast hardFamilyIndex_card_ge_four m n hm hn hsize
  have hb : 1024 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤
      Real.log (Fintype.card (HardFamilyIndex m n)) / 4 := by linarith
  have htest (d : Samples (Option (Fin m)) (Fin (n + 1)) N → HardFamilyIndex m n) :
      (1 : ℝ) / 4 ≤ (∑ i : HardFamilyIndex m n,
        (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real
          {data | d data ≠ i}) / Fintype.card (HardFamilyIndex m n) :=
    (fano_large_cardinality_quarter _ _ hk hb).trans
      (sourceFamily_average_error_fano hm hn γ ε hγ hγ1 hε hεmax N d)
  obtain ⟨i, hi⟩ := sourceFamily_averageTesting_to_policyRisk hm hn γ ε hγ hγ1 hε hεmax
    N (1 / 4) estimate htest
  exact ⟨i, lt_of_lt_of_le (by norm_num) hi⟩

end StatisticalRL.GenerativeLowerBound
