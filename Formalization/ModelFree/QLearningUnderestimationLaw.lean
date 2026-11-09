import Formalization.ModelFree.QLearningUnderestimationLift
import Formalization.ModelFree.QLearningSynchronousSampling

/-! the exact-T Q-learning sampling law, lifted coordinatewise by
`s' ↦ (s', f s')`, is the exact-T TD sampling law of the lifted chain. The padded
TD law on `Fin (T+1)` is reached afterwards through the library projection
`tdUsedSampleProjection_map_law` (the `Fin.succ` marginal). -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
open StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance qLiftLawStateMeasurable : MeasurableSpace State := ⊤
local instance qLiftLawActionMeasurable : MeasurableSpace Action := ⊤
local instance qLiftLawPairMeasurable :
    MeasurableSpace (State × Action) := ⊤

theorem finiteDistribution_eq_of_prob {Ω : Type*} [Fintype Ω]
    {d₁ d₂ : FiniteDistribution Ω} (h : d₁.prob = d₂.prob) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

/-- Single-action mixture row: the policy row of the lifted chain is its unique
transition row. -/
theorem qPolicyLift_policyTransition (M : DiscountedMDP State Action) (f : State → Action)
    (x : State × Action) :
    (qPolicyLiftMDP M f).policyTransition qPolicyLiftPolicy x =
      qPolicyLiftTransition M f x.1 x.2 := by
  apply finiteDistribution_eq_of_prob
  funext y
  rw [DiscountedMDP.policyTransition_prob]
  unfold qPolicyLiftPolicy
  rw [EnvironmentStage.expectation_pointMass]
  rfl

/-- One lifted draw is the image of one transition draw under `s' ↦ (s', f s')`. -/
theorem qPolicyLift_rowMeasure (M : DiscountedMDP State Action) (f : State → Action)
    (s : State) (a : Action) :
    (M.transition s a).rowMeasure.map (fun s' ↦ (s', f s')) =
      (qPolicyLiftTransition M f s a).rowMeasure := by
  unfold FiniteDistribution.rowMeasure
  rw [PMF.toMeasure_map (hf := measurable_from_top)]
  congr 1
  ext y
  rw [PMF.map_apply, tsum_fintype]
  unfold FiniteDistribution.toPMF
  simp only [PMF.ofFintype_apply]
  unfold qPolicyLiftTransition FiniteDistribution.bind
  simp only [FiniteDistribution.expectation, EnvironmentStage.pointMass]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ mul_nonneg
    ((M.transition s a).prob_nonneg x) (by split <;> norm_num))]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

/-- Law identity: the coordinatewise lift pushes the exact-T Q-learning law onto
the exact-T TD law of the lifted chain. -/
theorem qSamplingLaw_map_qPolicyLiftData (M : DiscountedMDP State Action)
    (f : State → Action) (T : ℕ) :
    (qSamplingLaw M T).map (qPolicyLiftData f) =
      tdSourceSamplingLaw (qPolicyLiftMDP M f) qPolicyLiftPolicy T := by
  have hσ : ∀ i : (State × Action) × Fin T, SigmaFinite
      (((fun i : (State × Action) × Fin T ↦ (M.transition i.1.1 i.1.2).rowMeasure) i).map
        ((fun _ : (State × Action) × Fin T ↦ fun s' : State ↦ (s', f s')) i)) := by
    intro i
    show SigmaFinite ((M.transition i.1.1 i.1.2).rowMeasure.map (fun s' ↦ (s', f s')))
    rw [qPolicyLift_rowMeasure]
    unfold FiniteDistribution.rowMeasure
    infer_instance
  unfold qSamplingLaw ModelBasedPolicyLearning.samplingLaw tdSourceSamplingLaw
    ModelBasedPolicyEvaluation.samplingLaw
  change (Measure.pi (fun i : (State × Action) × Fin T ↦
      (M.transition i.1.1 i.1.2).rowMeasure)).map
        (fun data i ↦ (fun _ : (State × Action) × Fin T ↦ fun s' : State ↦ (s', f s')) i
          (data i)) = _
  rw [Measure.pi_map_pi (hμ := hσ) (fun _ ↦ measurable_from_top.aemeasurable)]
  congr 1
  funext i
  rw [qPolicyLift_policyTransition]
  exact qPolicyLift_rowMeasure M f i.1.1 i.1.2

/-- Event form of the law identity: the probability of a lifted-data event under the
Q-learning law equals its TD-law probability on the lifted chain. -/
theorem qSamplingLaw_real_preimage_qPolicyLiftData (M : DiscountedMDP State Action)
    (f : State → Action) (T : ℕ) (E : Set (TDSourceSamples (State × Action) T)) :
    (qSamplingLaw M T).real (qPolicyLiftData f ⁻¹' E) =
      (tdSourceSamplingLaw (qPolicyLiftMDP M f) qPolicyLiftPolicy T).real E := by
  have hm : Measurable (qPolicyLiftData (State := State) (Action := Action) f (T := T)) :=
    measurable_of_countable _
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← qSamplingLaw_map_qPolicyLiftData, measureReal_def, measureReal_def,
    Measure.map_apply hm hE]

end StatisticalRL.QLearning
