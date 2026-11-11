import Formalization.Generative.FiniteHorizonPolicyPerturbation
import Formalization.Probability.Variance

import Formalization.Generative.ModelBasedDefinitions
/-! The true-variance-derived forcing/value recursion of Li et al. (61)-(62).
Higher-level forcing is not constrained to the original reward interval.
No growth estimate or conditional Lemma 9 premise is assumed. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance auxiliaryVarianceStateMeasurable : MeasurableSpace State := ⊤

/-- True auxiliary values, defined backwards in episode time at every level.
The level-successor forcing is the true-row conditional standard deviation
of the preceding level's true next-stage value. -/
noncomputable def trueAuxiliaryValue : List (EnvironmentStage State Action) →
    (ℕ → State → Action) → ℕ → State → ℝ
  | [], _, _ => fun _ ↦ 0
  | E :: es, f, 0 => fun s ↦ E.reward s (f 0 s) +
      (E.transition s (f 0 s)).expectation (trueAuxiliaryValue es (fun k ↦ f (k + 1)) 0)
  | E :: es, f, l + 1 => fun s ↦
      Real.sqrt ((E.transition s (f 0 s)).variance (trueAuxiliaryValue es (fun k ↦ f (k + 1)) l)) +
      (E.transition s (f 0 s)).expectation (trueAuxiliaryValue es (fun k ↦ f (k + 1)) (l + 1))

/-- Shared forcing: original reward at level zero and true-variance-derived
standard deviation at higher levels. It is never recomputed from empirical P. -/
noncomputable def auxiliaryPolicyReward : List (EnvironmentStage State Action) →
    (ℕ → State → Action) → ℕ → State → ℝ
  | [], _, _ => fun _ ↦ 0
  | E :: _, f, 0 => fun s ↦ E.reward s (f 0 s)
  | E :: es, f, l + 1 => fun s ↦
      Real.sqrt ((E.transition s (f 0 s)).variance (trueAuxiliaryValue es (fun k ↦ f (k + 1)) l))

/-- Comparison values use exactly the same true-derived forcing and fixed
policy, with only the transition propagation replaced by the comparison row. -/
noncomputable def comparisonAuxiliaryValue :
    List (EnvironmentStage State Action × EnvironmentStage State Action) →
      (ℕ → State → Action) → ℕ → State → ℝ
  | [], _, _ => fun _ ↦ 0
  | (E,F) :: tail, f, l => fun s ↦
      auxiliaryPolicyReward (E :: tail.map Prod.fst) f l s +
      (F.transition s (f 0 s)).expectation (comparisonAuxiliaryValue tail (fun k ↦ f (k + 1)) l)

theorem trueAuxiliaryValue_bellman (E : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (l : ℕ) (s : State) :
    trueAuxiliaryValue (E :: es) f l s = auxiliaryPolicyReward (E :: es) f l s +
      (E.transition s (f 0 s)).expectation (trueAuxiliaryValue es (fun k ↦ f (k + 1)) l) := by
  cases l <;> rfl

theorem comparisonAuxiliaryValue_bellman (E F : EnvironmentStage State Action)
    (tail : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) :
    comparisonAuxiliaryValue ((E,F) :: tail) f l s =
      auxiliaryPolicyReward (E :: tail.map Prod.fst) f l s +
      (F.transition s (f 0 s)).expectation (comparisonAuxiliaryValue tail (fun k ↦ f (k + 1)) l) := rfl

theorem auxiliaryPolicyReward_nonneg (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) : 0 ≤ auxiliaryPolicyReward es f l s := by
  cases es with
  | nil => exact le_rfl
  | cons E es => cases l with
    | zero => exact E.reward_nonneg s (f 0 s)
    | succ l => exact Real.sqrt_nonneg _

theorem trueAuxiliaryValue_nonneg (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) : 0 ≤ trueAuxiliaryValue es f l s := by
  induction es generalizing f l s with
  | nil => exact le_rfl
  | cons E es ih =>
    rw [trueAuxiliaryValue_bellman]
    exact add_nonneg (auxiliaryPolicyReward_nonneg _ f l s)
      ((E.transition s (f 0 s)).expectation_nonneg (fun t ↦ ih _ l t))

theorem comparisonAuxiliaryValue_nonneg
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) : 0 ≤ comparisonAuxiliaryValue pairs f l s := by
  induction pairs generalizing f l s with
  | nil => exact le_rfl
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    exact add_nonneg (auxiliaryPolicyReward_nonneg _ f l s)
      ((F.transition s (f 0 s)).expectation_nonneg (fun t ↦ ih _ l t))

/-- Level zero is independently identified with the actual ordinary finite
trajectory expectation under the fixed deterministic policy. -/
theorem trueAuxiliaryValue_zero_eq_trajectory
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (s : State) :
    trueAuxiliaryValue es f 0 s =
      DecisionStage.trajectoryValue (EnvironmentStage.controlled es (deterministicPolicy f)) s := by
  induction es generalizing f s with
  | nil => simp [trueAuxiliaryValue, EnvironmentStage.controlled, DecisionStage.trajectoryValue_nil]
  | cons E es ih =>
    rw [EnvironmentStage.controlled, DecisionStage.trajectoryValue_cons]
    change E.reward s (f 0 s) + (E.transition s (f 0 s)).expectation
      (trueAuxiliaryValue es (fun k ↦ f (k + 1)) 0) =
      (EnvironmentStage.pointMass (f 0 s)).expectation (fun a ↦ E.reward s a +
        (E.transition s a).expectation (DecisionStage.trajectoryValue
          (EnvironmentStage.controlled es (deterministicPolicy (fun k ↦ f (k + 1))))))
    rw [EnvironmentStage.expectation_pointMass]
    congr 1
    exact congrArg (E.transition s (f 0 s)).expectation (funext (fun t ↦ ih _ t))

/-- The empirical/comparison level-zero bridge uses the same known rewards;
higher-level forcing is shared by construction rather than bounded by one. -/
theorem comparisonAuxiliaryValue_zero_eq_trajectory
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) (s : State) :
    comparisonAuxiliaryValue pairs f 0 s =
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.snd) (deterministicPolicy f)) s := by
  induction pairs generalizing f s with
  | nil => simp [comparisonAuxiliaryValue, EnvironmentStage.controlled, DecisionStage.trajectoryValue_nil]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    have hh : F.reward = E.reward := hr (E,F) (by simp)
    have ht : ∀ p ∈ tail, p.2.reward = p.1.reward := fun p hp ↦ hr p (by simp [hp])
    rw [List.map_cons, EnvironmentStage.controlled, DecisionStage.trajectoryValue_cons]
    change E.reward s (f 0 s) + (F.transition s (f 0 s)).expectation
      (comparisonAuxiliaryValue tail (fun k ↦ f (k + 1)) 0) =
      (EnvironmentStage.pointMass (f 0 s)).expectation (fun a ↦ F.reward s a +
        (F.transition s a).expectation (DecisionStage.trajectoryValue
          (EnvironmentStage.controlled (tail.map Prod.snd) (deterministicPolicy (fun k ↦ f (k + 1))))))
    rw [EnvironmentStage.expectation_pointMass, hh]
    congr 1
    exact congrArg (F.transition s (f 0 s)).expectation (funext (fun t ↦ ih _ ht t))

noncomputable def trueAuxiliaryValueAt (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l h : ℕ) : State → ℝ :=
  trueAuxiliaryValue (es.drop h) (fun k ↦ f (h + k)) l

noncomputable def comparisonAuxiliaryValueAt
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l h : ℕ) : State → ℝ :=
  comparisonAuxiliaryValue (pairs.drop h) (fun k ↦ f (h + k)) l

theorem trueAuxiliaryValueAt_terminal (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) : trueAuxiliaryValueAt es f l es.length = fun _ ↦ 0 := by
  simp [trueAuxiliaryValueAt, trueAuxiliaryValue]

theorem comparisonAuxiliaryValueAt_terminal
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) : comparisonAuxiliaryValueAt pairs f l pairs.length = fun _ ↦ 0 := by
  simp [comparisonAuxiliaryValueAt, comparisonAuxiliaryValue]

/-- Every level depends only on the remaining stage pairs and remaining
policy choices. No dependence on discarded past stages is introduced. -/
theorem comparisonAuxiliaryValueAt_suffix_congr
    (pairs₁ pairs₂ : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f g : ℕ → State → Action) (l h : ℕ)
    (hp : pairs₁.drop h = pairs₂.drop h) (hf : ∀ k s, f (h + k) s = g (h + k) s) :
    comparisonAuxiliaryValueAt pairs₁ f l h = comparisonAuxiliaryValueAt pairs₂ g l h := by
  unfold comparisonAuxiliaryValueAt
  rw [hp]
  congr 1
  funext k s
  exact hf k s

theorem trueAuxiliaryValueAt_suffix_congr
    (es fs : List (EnvironmentStage State Action)) (f g : ℕ → State → Action) (l h : ℕ)
    (he : es.drop h = fs.drop h) (hf : ∀ k s, f (h + k) s = g (h + k) s) :
    trueAuxiliaryValueAt es f l h = trueAuxiliaryValueAt fs g l h := by
  unfold trueAuxiliaryValueAt
  rw [he]
  congr 1
  funext k s
  exact hf k s

/-- Same-data auxiliary empirical values, with the source's shared true-derived
forcing at all levels rather than fresh empirical variance rewards. -/
noncomputable def empiricalAuxiliaryValueAt {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N)
    (f : ℕ → State → Action) (l h : ℕ) : State → ℝ :=
  comparisonAuxiliaryValueAt (pairedEmpiricalStages E N hN data) f l h

theorem empiricalAuxiliaryValue_zero_eq_trajectory {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) (f : ℕ → State → Action) (s : State) :
    empiricalAuxiliaryValueAt E N hN data f 0 0 s =
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (empiricalStages E N hN data) (deterministicPolicy f)) s := by
  have hr : ∀ p ∈ pairedEmpiricalStages E N hN data, p.2.reward = p.1.reward := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    rw [← hi]
    rfl
  have hp := comparisonAuxiliaryValue_zero_eq_trajectory (pairedEmpiricalStages E N hN data) f hr s
  simpa only [empiricalAuxiliaryValueAt, comparisonAuxiliaryValueAt, List.drop_zero, Nat.zero_add,
    pairedEmpiricalStages, List.map_ofFn, Function.comp_def, empiricalStages] using hp

/-- Literal paired-stage suffix equality when all future row samples agree. -/
theorem pairedEmpiricalStages_drop_eq_of_future_eq {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (data₁ data₂ : Samples State Action H N)
    (he : ∀ j : Fin H, h < j → ∀ s a i, data₁ ((j,s,a),i) = data₂ ((j,s,a),i)) :
    (pairedEmpiricalStages E N hN data₁).drop (h.val + 1) =
      (pairedEmpiricalStages E N hN data₂).drop (h.val + 1) := by
  apply List.ext_getElem
  · simp [pairedEmpiricalStages]
  · intro i hi hj
    simp only [pairedEmpiricalStages, List.length_drop, List.length_ofFn] at hi hj
    have hidx : h.val + 1 + i < H := by omega
    simp only [pairedEmpiricalStages, List.getElem_drop, List.getElem_ofFn]
    apply Prod.ext
    · rfl
    apply empiricalStage_eq_of_data_eq
    exact he ⟨h.val + 1 + i, hidx⟩ (by change h.val < h.val + 1 + i; omega)

/-- Every empirical auxiliary level, for a fixed policy, factors through the
same strictly-future sample block at the next stage. -/
theorem empiricalAuxiliaryValueAt_factors_future {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (x : State) (data : Samples State Action H N)
    (f : ℕ → State → Action) (l : ℕ) :
    empiricalAuxiliaryValueAt E N hN data f l (h.val + 1) =
      empiricalAuxiliaryValueAt E N hN (completeFutureData h N x (futureData h N data)) f l (h.val + 1) := by
  apply comparisonAuxiliaryValueAt_suffix_congr
  · apply pairedEmpiricalStages_drop_eq_of_future_eq
    intro j hj s a i
    simp [completeFutureData, futureData, hj]
  · intro k s
    rfl

theorem empiricalAuxiliaryValueAt_measurable {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (f : ℕ → State → Action) (l h : ℕ) :
    Measurable (fun data ↦ empiricalAuxiliaryValueAt E N hN data f l h) := measurable_of_countable _

/-- For a fixed deterministic policy the actual empirical auxiliary next-stage
vector is independent of the complete current row, at every fixed level. -/
theorem empiricalAuxiliaryValueAt_indep_row {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (s : State) (a : Action) (f : ℕ → State → Action) (l : ℕ) :
    IndepFun (fun data ↦ empiricalAuxiliaryValueAt E N hN data f l (h.val + 1))
      (fun data : Samples State Action H N ↦ fun i : Fin N ↦ data ((h,s,a),i)) (samplingLaw E N) := by
  let x := Classical.choice (E h).state_nonempty
  let F : FutureCode (State := State) (Action := Action) h N → State → ℝ :=
    fun code ↦ empiricalAuxiliaryValueAt E N hN (completeFutureData h N x code) f l (h.val + 1)
  have hp := futureStatistic_indep_row E N h s a F
  have he : (fun data ↦ F (futureData h N data)) =
      (fun data ↦ empiricalAuxiliaryValueAt E N hN data f l (h.val + 1)) := by
    funext data
    exact (empiricalAuxiliaryValueAt_factors_future E N hN h x data f l).symm
  rw [he] at hp
  exact hp

end StatisticalRL.FiniteHorizonGenerative
