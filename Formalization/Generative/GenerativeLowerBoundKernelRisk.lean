import Formalization.Generative.GenerativeLowerBoundFiniteKernelSeed
import Formalization.Generative.GenerativeLowerBoundSeededLargeRisk
import Formalization.Generative.GenerativeLowerBoundSeededTwoPointRisk
import Formalization.Generative.GenerativeLowerBoundUnifiedThreshold

/-! Corrected family lower bound for finite-output randomized estimators. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance kernelRiskState (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance kernelRiskFin (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- For every common data-dependent PMF over deterministic stationary policies,
one corrected-family model has strict >0.1 actual joint-law trajectory-Q risk.
The policy output itself is deterministic; the estimator may randomize. -/
theorem sourceFamily_kernel_policy_risk {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
      Real.log ((m + 1 : ℕ) * (n + 1)))
    (κ : Samples (Option (Fin m)) (Fin (n + 1)) N →
      PMF (Option (Fin m) → Fin (n + 1))) :
    ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 10 < (finiteKernelJointLaw (samplingLaw M N) κ).real
        {z | ε < ‖M.trajectoryExpectedQ (deterministicFamilyPolicy z.2) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  let X := Samples (Option (Fin m)) (Fin (n + 1)) N
  let Y := Option (Fin m) → Fin (n + 1)
  let σ : Measure (X → Y) := (finiteKernelSeed κ).toMeasure
  haveI : IsProbabilityMeasure σ := by dsimp [σ]; infer_instance
  let est : X × (X → Y) → Y := fun z ↦ z.2 z.1
  have ht : 0 ≤ (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by
    have hg : 0 ≤ 1 - γ := by linarith
    positivity
  have hb := correctedFamily_common_budget m n hm hn _ ht hbudget
  have hr : ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 10 < (independentSeedLaw (samplingLaw M N) σ).real
        {z | ε < ‖M.trajectoryExpectedQ (deterministicFamilyPolicy (est z)) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
    rcases hb with ⟨hsize, hlarge⟩ | ⟨hsize, hsmall⟩
    · apply sourceFamily_seeded_large_policy_risk hm hn hsize γ ε hγ hγ1 hε hεmax N _ σ est
      nlinarith
    · apply sourceFamily_seeded_twoPoint_policy_risk hm hn γ ε hγ hγ1 hε hεmax N _ σ est
      nlinarith
  obtain ⟨i, hi⟩ := hr
  refine ⟨i, ?_⟩
  let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
  have hmap := finiteKernelSeed_joint_law (samplingLaw M N) κ
  change (1 : ℝ) / 10 < (finiteKernelJointLaw (samplingLaw M N) κ).real _
  rw [← hmap]
  simp only [measureReal_def, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  exact hi

end StatisticalRL.GenerativeLowerBound
