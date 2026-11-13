import Formalization.ModelFree.QLearningSamplingDefinitions
import Formalization.ModelFree.TDSourceSamplingDefinitions
import Formalization.ModelFree.TDIterateBounds
import Formalization.Probability.EmpiricalRow
import Formalization.MDP.ForcedPrefixBridge
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Single-action synchronous Q-learning is TD learning (O4)

Remark 4.5 (`chapters/generative_model_model_free.tex:3455–3457`) contrasts `A = 1` with
`A ≥ 2`: with a single action the max operator disappears, and the sample complexity has the TD
horizon dependence `(1−γ)⁻³`. This module proves the identification that this rests on.

When the action set has one element `a` (`Subsingleton Action`):

* `qLearningIterate_singleAction`: synchronous Q-learning (`qLearningIterate`) with next-state
  samples `s'(t,s,a)` and initial `Q₀` equals, at action `a`, TD learning (`tdIterate`) for any
  (necessarily the unique) policy with samples `s'(t,s,a)` and initial `Q₀(·,a)`, pathwise;
* `qSampledIterate_singleAction`: the same for the exact-`T` sample arrays, through the
  projection that drops the action coordinate;
* `qSamplingLaw_map_singleActionProjection`: that projection maps the exact-`T` Q-learning sample
  law onto the exact-`T` TD sample law;
* `qSampled_singleAction_event_eq`: hence every event about the output of `T` steps of
  Q-learning (at action `a`) has the same probability as the corresponding event about `T` steps
  of TD learning;
* `optimalQ_singleAction_eq_value`: `Q⋆(s,a) = V^π(s)`, so the Q-learning error
  `|Q_T(s,a) − Q⋆(s,a)|` is the TD error `|V_T(s) − V^π(s)|`.
-/

open MeasureTheory

namespace StatisticalRL.QLearning

open StatisticalRL.TemporalDifference

/-- Two finite probability vectors with the same masses are equal. -/
theorem finiteDistribution_ext {Ω : Type*} [Fintype Ω] {d e : FiniteDistribution Ω}
    (h : ∀ x, d.prob x = e.prob x) : d = e :=
  FiniteDistribution.ext (funext h)

variable {State Action : Type*} [Fintype State] [Fintype Action] [Subsingleton Action]

/-- With one action, every probability vector on actions is the same. -/
theorem finiteDistribution_eq_of_subsingleton (d e : FiniteDistribution Action) : d = e :=
  FiniteDistribution.eq_of_subsingleton d e

/-- With one action `a`, the policy transition row is the row of `a`. -/
theorem policyTransition_singleAction (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (s : State) :
    M.policyTransition π s = M.transition s a := by
  refine finiteDistribution_ext fun t ↦ ?_
  rw [DiscountedMDP.policyTransition_prob]
  have hconst : (fun b ↦ (M.transition s b).prob t) = fun _ ↦ (M.transition s a).prob t :=
    funext fun b ↦ by rw [Subsingleton.elim b a]
  rw [hconst, FiniteDistribution.expectation_const]

/-- With one action `a`, the policy reward is the reward of `a`. -/
theorem policyReward_singleAction (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (s : State) :
    policyReward M π s = M.reward s a := by
  unfold policyReward DiscountedMDP.policyExpectedReward
  have hconst : M.reward s = fun _ ↦ M.reward s a :=
    funext fun b ↦ by rw [Subsingleton.elim b a]
  rw [hconst, FiniteDistribution.expectation_const]

/-- With one action `a`, the maximum over actions is the value at `a`. -/
theorem qLearningValue_singleAction (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (a : Action) (s : State) :
    qLearningValue M Q s = Q s a := by
  letI : Nonempty Action := M.action_nonempty
  change actionMaximum (Q s) = Q s a
  unfold actionMaximum
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun b _ ↦ by rw [Subsingleton.elim b a]
  · exact Finset.le_sup' (Q s) (Finset.mem_univ a)

/-- Pathwise: single-action synchronous Q-learning at action `a` is TD learning with the
samples of `a`. -/
theorem qLearningIterate_singleAction (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ) (t : ℕ) (s : State) :
    qLearningIterate M η samples Q₀ t s a =
      tdIterate M π η (fun k s ↦ samples k s a) (fun s ↦ Q₀ s a) t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      change (1 - η (t + 1)) * qLearningIterate M η samples Q₀ t s a +
          η (t + 1) * (M.reward s a + M.discount *
            qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t + 1) s a)) =
        (1 - η (t + 1)) * tdIterate M π η (fun k s ↦ samples k s a) (fun s ↦ Q₀ s a) t s +
          η (t + 1) * (policyReward M π s + M.discount *
            tdIterate M π η (fun k s ↦ samples k s a) (fun s ↦ Q₀ s a) t (samples (t + 1) s a))
      rw [qLearningValue_singleAction M _ a, policyReward_singleAction M π a, ih, ih]

/-- Drop the action coordinate of an exact-`T` Q-learning sample array. -/
def singleActionProjection (a : Action) (T : ℕ) (data : QSamples State Action T) :
    TDSourceSamples State T :=
  fun i ↦ data ((i.1, a), i.2)

/-- Exact-`T` form of `qLearningIterate_singleAction`. -/
theorem qSampledIterate_singleAction (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (η : ℕ → ℝ) (T : ℕ)
    (Q₀ : State → Action → ℝ) (data : QSamples State Action T) (s : State) :
    qSampledIterate M η T Q₀ data s a =
      tdSourceSampledIterate M π η T (fun s ↦ Q₀ s a) (singleActionProjection a T data) s := by
  unfold qSampledIterate tdSourceSampledIterate
  rw [qLearningIterate_singleAction M π a]
  have hext : (fun k s ↦ qSamplesExtend M T data k s a) =
      tdSourceSamplesExtend M T (singleActionProjection a T data) := by
    funext k s
    unfold qSamplesExtend tdSourceSamplesExtend singleActionProjection
    split_ifs with h1 h2 h2
    · rfl
    · omega
    · omega
    · rfl
  rw [hext]

/-- The coordinate equivalence `(s, i) ↦ ((s, a), i)` for a one-element action set. -/
def singleActionIndexEquiv (a : Action) (T : ℕ) : State × Fin T ≃ (State × Action) × Fin T where
  toFun i := ((i.1, a), i.2)
  invFun j := (j.1.1, j.2)
  left_inv i := rfl
  right_inv j := by
    obtain ⟨⟨s, b⟩, i⟩ := j
    rw [Subsingleton.elim b a]

section Law

local instance singleActionStateMeasurable : MeasurableSpace State := ⊤

omit [Fintype State] [Fintype Action] [Subsingleton Action] in
theorem measurable_singleActionProjection (a : Action) (T : ℕ) :
    Measurable (singleActionProjection (State := State) a T) :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply ((i.1, a), i.2)

/-- Every set of exact-`T` TD sample arrays is measurable (finite product of discrete spaces). -/
theorem measurableSet_tdSourceSamples (T : ℕ) (B : Set (TDSourceSamples State T)) :
    MeasurableSet B := by
  have hs : ∀ g : TDSourceSamples State T, MeasurableSet ({g} : Set (TDSourceSamples State T)) := by
    intro g
    have : ({g} : Set (TDSourceSamples State T)) = ⋂ i, (fun f ↦ f i) ⁻¹' {g i} := by
      ext f
      simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i ↦ measurable_pi_apply i MeasurableSpace.measurableSet_top
  rw [← Set.biUnion_of_singleton B]
  exact MeasurableSet.biUnion (Set.toFinite B).countable fun g _ ↦ hs g

/-- In law: dropping the action coordinate maps the exact-`T` Q-learning sample law of a
one-action MDP onto the exact-`T` TD sample law of its (unique) policy. -/
theorem qSamplingLaw_map_singleActionProjection (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (T : ℕ) :
    (qSamplingLaw M T).map (singleActionProjection a T) = tdSourceSamplingLaw M π T := by
  have hmp := (measurePreserving_piCongrLeft
    (fun i : (State × Action) × Fin T ↦ (M.transition i.1.1 i.1.2).rowMeasure)
    (singleActionIndexEquiv (State := State) a T)).symm
    (MeasurableEquiv.piCongrLeft (fun _ ↦ State) (singleActionIndexEquiv a T))
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ ↦ State) (singleActionIndexEquiv a T)).symm =
      singleActionProjection (State := State) a T := by
    funext g i
    rfl
  rw [hfun] at hmp
  change (Measure.pi fun i : (State × Action) × Fin T ↦
      (M.transition i.1.1 i.1.2).rowMeasure).map (singleActionProjection a T) = _
  rw [hmp.map_eq]
  change _ = Measure.pi (fun i : State × Fin T ↦ (M.policyTransition π i.1).rowMeasure)
  congr 1
  funext i
  change (M.transition i.1 a).rowMeasure = (M.policyTransition π i.1).rowMeasure
  rw [policyTransition_singleAction M π a]

/-- Every event about `T` steps of single-action Q-learning (read at the action `a`) has the same
probability as the corresponding event about `T` steps of TD learning. -/
theorem qSampled_singleAction_event_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (η : ℕ → ℝ) (T : ℕ)
    (Q₀ : State → Action → ℝ) (B : Set (State → ℝ)) :
    (qSamplingLaw M T).real {data | (fun s ↦ qSampledIterate M η T Q₀ data s a) ∈ B} =
      (tdSourceSamplingLaw M π T).real
        {data | tdSourceSampledIterate M π η T (fun s ↦ Q₀ s a) data ∈ B} := by
  rw [← qSamplingLaw_map_singleActionProjection M π a T,
    map_measureReal_apply (measurable_singleActionProjection a T)
      (measurableSet_tdSourceSamples T _)]
  congr 1
  ext data
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have : (fun s ↦ qSampledIterate M η T Q₀ data s a) =
      tdSourceSampledIterate M π η T (fun s ↦ Q₀ s a) (singleActionProjection a T data) :=
    funext fun s ↦ qSampledIterate_singleAction M π a η T Q₀ data s
  rw [this]

end Law

/-- With one action, `Q⋆(s,a)` (actual trajectory Q of the optimal greedy policy) equals the
policy value `V^π(s)` of the unique policy. -/
theorem optimalQ_singleAction_eq_value (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (a : Action) (s : State) :
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a = M.trajectoryExpectedValue π s := by
  have hπ : M.optimalGreedyPolicy = π :=
    funext fun s ↦ finiteDistribution_eq_of_subsingleton _ _
  rw [hπ, M.trajectoryExpectedValue_eq_policyAverageQ π s]
  have hconst : M.trajectoryExpectedQ π s = fun _ ↦ M.trajectoryExpectedQ π s a :=
    funext fun b ↦ by rw [Subsingleton.elim b a]
  rw [hconst, FiniteDistribution.expectation_const]

end StatisticalRL.QLearning
