import Formalization.Generative.FiniteHorizonAuxiliaryVariance

import Formalization.Generative.ModelBasedDefinitions
/-! Causal backward-greedy policy selection and its TRUE auxiliary continuation.
This is distinct from a fixed policy's empirical auxiliary value family. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance fittedAuxiliaryStateMeasurable : MeasurableSpace State := ⊤

theorem backwardGreedyActions_drop (fallback : Action)
    (es : List (EnvironmentStage State Action)) (h k : ℕ) (s : State) :
    backwardGreedyActions fallback es (h + k) s =
      backwardGreedyActions fallback (es.drop h) k s := by
  induction h generalizing es with
  | zero => simp
  | succ h ih =>
    cases es with
    | nil => simp [backwardGreedyActions]
    | cons E es =>
      simpa only [Nat.succ_add, backwardGreedyActions, List.drop_succ_cons] using ih es

/-- The concrete action selector realizes the actual existing greedy stage process. -/
theorem controlled_backwardGreedyActions (fallback : Action)
    (es : List (EnvironmentStage State Action)) :
    EnvironmentStage.controlled es (deterministicPolicy (backwardGreedyActions fallback es)) =
      EnvironmentStage.greedyStages es := by
  induction es with
  | nil => rfl
  | cons E es ih =>
    change E.withPolicy (fun s ↦ EnvironmentStage.pointMass
      (E.greedyAction (EnvironmentStage.optimalValue es) s)) ::
      EnvironmentStage.controlled es (deterministicPolicy (backwardGreedyActions fallback es)) = _
    rw [ih]
    rfl

/-- This selected policy is an exact optimizer for the comparison environment. -/
theorem backwardGreedyActions_optimalValue (fallback : Action)
    (es : List (EnvironmentStage State Action)) (s : State) :
    DecisionStage.trajectoryValue (EnvironmentStage.controlled es
      (deterministicPolicy (backwardGreedyActions fallback es))) s =
      EnvironmentStage.optimalValue es s := by
  rw [controlled_backwardGreedyActions]
  exact EnvironmentStage.greedy_trajectoryValue es s

/-- The actual true-model auxiliary value evaluated at the empirical backward
planner's policy, after the current stage. Its policy is selected from data. -/
noncomputable def fittedTrueAuxiliaryContinuation {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (h : Fin H) (l : ℕ) (data : Samples State Action H N) : State → ℝ :=
  trueAuxiliaryValueAt (List.ofFn E)
    (backwardGreedyActions fallback (empiricalStages E N hN data)) l (h.val + 1)

/-- At level zero this is an actual true-model policy trajectory value, with
the fitted suffix policy rather than the empirical optimal value substituted. -/
theorem fittedTrueAuxiliaryContinuation_zero_eq_trajectory {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (h : Fin H) (data : Samples State Action H N) (s : State) :
    fittedTrueAuxiliaryContinuation E N hN fallback h 0 data s =
      DecisionStage.trajectoryValue (EnvironmentStage.controlled ((List.ofFn E).drop (h.val + 1))
        (deterministicPolicy (fun k ↦ backwardGreedyActions fallback
          (empiricalStages E N hN data) (h.val + 1 + k)))) s :=
  trueAuxiliaryValue_zero_eq_trajectory _ _ _

/-- All selected suffix decisions are functions of future empirical stages;
no current-row information enters through tie breaking. -/
theorem fittedTrueAuxiliaryContinuation_factors_future {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (h : Fin H) (l : ℕ) (x : State) (data : Samples State Action H N) :
    fittedTrueAuxiliaryContinuation E N hN fallback h l data =
      fittedTrueAuxiliaryContinuation E N hN fallback h l
        (completeFutureData h N x (futureData h N data)) := by
  apply trueAuxiliaryValueAt_suffix_congr
  · rfl
  · intro k s
    rw [backwardGreedyActions_drop, backwardGreedyActions_drop]
    have he := empiricalStages_drop_eq_of_future_eq E N hN h data
      (completeFutureData h N x (futureData h N data)) (by
        intro j hj t a i
        simp [completeFutureData, futureData, hj])
    rw [he]

theorem fittedTrueAuxiliaryContinuation_nonneg {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (h : Fin H) (l : ℕ) (data : Samples State Action H N) (s : State) :
    0 ≤ fittedTrueAuxiliaryContinuation E N hN fallback h l data s :=
  trueAuxiliaryValue_nonneg _ _ _ _

theorem fittedTrueAuxiliaryContinuation_measurable {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (h : Fin H) (l : ℕ) :
    Measurable (fittedTrueAuxiliaryContinuation E N hN fallback h l) := measurable_of_countable _

/-- Independence follows from causal factorization and the actual product law,
not from assuming a data-selected policy is independent of its training samples. -/
theorem fittedTrueAuxiliaryContinuation_indep_row {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (h : Fin H) (l : ℕ) (s : State) (a : Action) :
    IndepFun (fittedTrueAuxiliaryContinuation E N hN fallback h l)
      (fun data : Samples State Action H N ↦ fun i : Fin N ↦ data ((h,s,a),i)) (samplingLaw E N) := by
  let x := Classical.choice (E h).state_nonempty
  let F : FutureCode (State := State) (Action := Action) h N → State → ℝ :=
    fun code ↦ fittedTrueAuxiliaryContinuation E N hN fallback h l (completeFutureData h N x code)
  have hp := futureStatistic_indep_row E N h s a F
  have he : (fun data ↦ F (futureData h N data)) = fittedTrueAuxiliaryContinuation E N hN fallback h l := by
    funext data
    exact (fittedTrueAuxiliaryContinuation_factors_future E N hN fallback h l x data).symm
  rw [he] at hp
  exact hp

end StatisticalRL.FiniteHorizonGenerative
