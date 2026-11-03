import Formalization.Obstructions.OneStateExperiment

/-!
# Source-facing formulation of the printed Theorem 3.7(ii)

Known rewards and discount are inputs to estimators; transition data are N
independent next-state draws per row. The formulation admits randomized
estimators driven by an arbitrary model-independent probability seed.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Obstructions

local instance sourceFinMeasurable (S : ℕ) : MeasurableSpace (Fin S) := ⊤

abbrev Theorem37Samples (S A N : ℕ) := ((Fin S × Fin A) × Fin N) → Fin S

/-- The full N-sample-per-row generative experiment for any admissible MDP. -/
noncomputable def theorem37GenerativeLaw {S A : ℕ}
    (M : DiscountedMDP (Fin S) (Fin A)) (N : ℕ) : Measure (Theorem37Samples S A N) :=
  Measure.pi (fun i : (Fin S × Fin A) × Fin N ↦ (M.transition i.1.1 i.1.2).rowMeasure)

instance theorem37GenerativeLaw_probability {S A : ℕ}
    (M : DiscountedMDP (Fin S) (Fin A)) (N : ℕ) :
    IsProbabilityMeasure (theorem37GenerativeLaw M N) := by
  unfold theorem37GenerativeLaw
  infer_instance

/-- Every indexed sample has the actual transition row's law. -/
theorem theorem37GenerativeLaw_marginal {S A : ℕ}
    (M : DiscountedMDP (Fin S) (Fin A)) (N : ℕ) (i : (Fin S × Fin A) × Fin N) :
    (theorem37GenerativeLaw M N).map (fun x ↦ x i) =
      (M.transition i.1.1 i.1.2).rowMeasure := by
  exact (measurePreserving_eval (fun i : (Fin S × Fin A) × Fin N ↦
    (M.transition i.1.1 i.1.2).rowMeasure) i).map_eq

/-- All queries are mutually independent, including distinct rows. -/
theorem theorem37GenerativeLaw_independent {S A : ℕ}
    (M : DiscountedMDP (Fin S) (Fin A)) (N : ℕ) :
    iIndepFun (fun i (x : Theorem37Samples S A N) ↦ x i) (theorem37GenerativeLaw M N) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- A Q-estimator takes known rewards, known discount, samples and a random
seed independent of the unknown model; its output is measurable in data/seed. -/
structure Theorem37QEstimator (S A N : ℕ) (Seed : Type*) [MeasurableSpace Seed] where
  estimate : (Fin S → Fin A → ℝ) → ℝ → (Theorem37Samples S A N × Seed) →
    Fin S → Fin A → ℝ
  estimate_measurable : ∀ r γ, Measurable (estimate r γ)

/-- The printed source assertion, under the explicit finite-product experiment
and measurable, independently seeded estimator interpretation. -/
def printedTheorem37ii : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S A N : ℕ) (γ ε : ℝ),
      16 ≤ S * A → (2 : ℝ) / 3 ≤ γ → γ < 1 →
      0 < ε → ε < 1 / (32 * (1 - γ)) →
      (N : ℝ) ≤ c * Real.log (S * A) / ((1 - γ) ^ 3 * ε ^ 2) →
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (est : Theorem37QEstimator S A N Seed),
        ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
          1 / 4 ≤ ((theorem37GenerativeLaw M N).prod ν).real {data |
            ε < ‖est.estimate M.reward M.discount data -
              (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖}

/-- A single admissible one-state estimator ignores both data and seed. -/
noncomputable def theorem37OneStateEstimator : Theorem37QEstimator 1 16 1 Unit where
  estimate r γ data := oneStateExperimentEstimator r γ data.1
  estimate_measurable r γ := (oneStateExperimentEstimator_measurable r γ).comp measurable_fst

/-- Every one-state model has zero actual trajectory Q-estimation loss at
every sample and seed, with its own known reward supplied to the same rule. -/
theorem theorem37OneStateEstimator_error (M : DiscountedMDP (Fin 1) (Fin 16))
    (data : Theorem37Samples 1 16 1 × Unit) :
    ‖theorem37OneStateEstimator.estimate M.reward M.discount data -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖ = 0 := by
  exact oneStateKnownRewardEstimator_norm_error M.reward M.discount M rfl rfl data.1

/-- Literal negation of the formalized printed claim. -/
theorem not_printedTheorem37ii : ¬ printedTheorem37ii := by
  rintro ⟨c, hc, H⟩
  obtain ⟨ε, hε, hεup, hγlo, hγhi, hsize, hN⟩ :=
    oneState_theorem37_hypotheses_feasible c hc
  let ν : Measure Unit := Measure.dirac ()
  haveI : IsProbabilityMeasure ν := inferInstance
  have hbound : ((1 : ℕ) : ℝ) ≤ c * Real.log (((1 : ℕ) : ℝ) * ((16 : ℕ) : ℝ)) /
      ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) := by simpa using hN
  obtain ⟨M, hM, hprob⟩ := H 1 16 1 ((2 : ℝ) / 3) ε (by norm_num)
    hγlo hγhi hε hεup hbound Unit ν theorem37OneStateEstimator
  have hempty : {data : Theorem37Samples 1 16 1 × Unit |
      ε < ‖theorem37OneStateEstimator.estimate M.reward M.discount data -
        (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} = ∅ := by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [theorem37OneStateEstimator_error]
    exact not_lt_of_ge hε.le
  rw [hempty] at hprob
  simp [Measure.real] at hprob
  norm_num at hprob

end StatisticalRL.Obstructions
