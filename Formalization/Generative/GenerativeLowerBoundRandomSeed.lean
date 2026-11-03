import Formalization.Generative.GenerativeLowerBoundPolicyGap
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Independent finite random seed and averaging of actual error events. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance randomSeedStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance randomSeedFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Product sampling law records an independent, hypothesis-independent
random seed whose law is chosen once and shared by every model. -/
noncomputable def independentSeedLaw {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (σ : Measure Ξ) : Measure (Ω × Ξ) := μ.prod σ

/-- For finite seed space, the actual joint probability of any event is the
seed-probability-weighted average of its fixed-seed sample probabilities. -/
theorem independentSeedLaw_real_event {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (μ : Measure Ω) (σ : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure σ]
    (E : Set (Ω × Ξ)) :
    (independentSeedLaw μ σ).real E =
      ∑ r, μ.real {x | (x, r) ∈ E} * σ.real {r} := by
  classical
  rw [measureReal_def, independentSeedLaw, Measure.prod_apply_symm (Set.to_countable E).measurableSet,
    lintegral_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, measureReal_def]
    rfl
  · intro r _
    exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top σ _)

/-- The same pointwise decoder-to-Q-loss implication remains valid for any
single seeded policy estimator under the independent product law. -/
theorem seeded_decoder_error_le_Q_risk {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (i : HardFamilyIndex m n) (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (σ : Measure Ξ) [IsProbabilityMeasure σ]
    (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N × Ξ → Option (Fin m) → Fin (n + 1)) :
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    let μ := independentSeedLaw (samplingLaw M N) σ
    μ.real {z | decodeHardPolicy (fun j ↦ estimate z (some j)) ≠ i} ≤
    μ.real {z | ε < ‖M.trajectoryExpectedQ (deterministicFamilyPolicy (estimate z)) -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  letI : IsProbabilityMeasure (independentSeedLaw
      (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N) σ) := by
    unfold independentSeedLaw
    infer_instance
  exact sourceFamilyMDP_decoder_error_probability_le_source_Q_risk _ hm hn i γ ε hγ hγ1 hε hεmax estimate

end StatisticalRL.GenerativeLowerBound
