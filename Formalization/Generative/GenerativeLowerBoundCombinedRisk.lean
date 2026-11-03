import Formalization.Generative.GenerativeLowerBoundKernelQuarter
import Formalization.Generative.GenerativeLowerBoundQMixtureFinalRandomized

/-! Proposed restricted-domain correction combining policy-risk and
randomized-Q-risk lower bounds under one universal sample constant.

This combines the two corrected lower bounds under one stronger sample
condition and explicit nondegenerate dimensions. It retains separate hard
models for the policy and Q estimators, as the source theorem does; it does
not claim one model makes both estimators fail simultaneously. It retains the
explicit `S≥2`, `A≥2`, and `SA≥16` restrictions. The first two are proposed
corrections and are not both explicit in the printed theorem.
-/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning

local instance combinedRiskStateMeasurable (m : ℕ) :
    MeasurableSpace (Option (Fin m)) := ⊤
local instance combinedRiskActionMeasurable (A : ℕ) :
    MeasurableSpace (Fin A) := ⊤

/-- Under one universal sample constant `c_N=1/32768`, both corrected
source-regime risks are at least one quarter. The two existential MDPs may
differ, matching the separate model quantifiers in Theorem 3.7(i),(ii). -/
theorem sourcePolicyAndQ_risk_quarter_with_common_constant
    {m n : ℕ} (hS : 2 ≤ m + 1) (hA : 2 ≤ n + 1)
    (hSA : 16 ≤ (m + 1) * (n + 1))
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
      Real.log ((m + 1) * (n + 1))) :
    (∀ κPolicy : Samples (Option (Fin m)) (Fin (n + 1)) N →
        PMF (Option (Fin m) → Fin (n + 1)),
      ∃ iPolicy : HardFamilyIndex m n,
      let M := sourceFamilyMDP iPolicy γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 4 ≤ (finiteKernelJointLaw (samplingLaw M N) κPolicy).real
        {z | ε < ‖M.trajectoryExpectedQ
          (deterministicFamilyPolicy z.2) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖}) ∧
    (∀ κQ : Samples (Option (Fin m)) (Fin (n + 1)) N →
        Measure (Option (Fin m) → Fin (n + 1) → ℝ),
      (∀ data, IsProbabilityMeasure (κQ data)) →
      ∃ iQ : QMixtureIndex m (n + 1),
      let M := qMixtureSourceMDP iQ γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 4 ≤ (finiteDataRandomOutputLaw (samplingLaw M N) κQ).real
        (Set.univ ×ˢ {Qhat |
          ε < ‖Qhat - M.trajectoryExpectedQ M.optimalGreedyPolicy‖})) := by
  have hm : 1 ≤ m := by omega
  have hn : 1 ≤ n := by omega
  constructor
  · intro κPolicy
    have hPolicyBudget :
        32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
          Real.log ((m + 1 : ℕ) * (n + 1)) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hbudget
    exact sourceFamily_kernel_policy_risk_quarter hm hn hSA γ ε hγ hγ1
      hε hεmax N hPolicyBudget κPolicy
  · intro κQ hκQ
    have hQBudget :
        512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
          Real.log ((m + 1) * (n + 1)) := by
      have hgap : 0 ≤ 1 - γ := by linarith
      have hterm : 0 ≤ (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by positivity
      have hscale : 512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
          32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) := by nlinarith
      exact hscale.trans hbudget
    have hQBudget' :
        512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
          Real.log ((m + 1) * (n + 1 : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hQBudget
    exact qMixtureSource_randomized_Q_risk hm hA hSA γ ε hγ hγ1
      hε hεmax N hQBudget' κQ hκQ

end StatisticalRL.GenerativeLowerBound
