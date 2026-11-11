import Formalization.Generative.FiniteHorizonGenerativeSampling
import Mathlib.Data.List.OfFn

import Formalization.Generative.ModelBasedDefinitions
/-! Actual empirical optimal continuation values factor through strictly
future stage samples. No statistical sample-complexity bound is claimed. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance finiteContinuationStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance finiteContinuationStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance finiteContinuationActionDecidable : DecidableEq Action := Classical.decEq Action

theorem empiricalStages_length {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) :
    (empiricalStages E N hN data).length = H := by simp [empiricalStages]

/-- Actual expected trajectory value of backward-optimal empirical planning
after the current stage h, including the zero terminal suffix. -/
noncomputable def empiricalContinuationValue {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (h : Fin H) (data : Samples State Action H N) : State → ℝ :=
  DecisionStage.trajectoryValue (EnvironmentStage.greedyStages
    ((empiricalStages E N hN data).drop (h.val + 1)))

theorem empiricalContinuationValue_eq_optimalValue {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (data : Samples State Action H N) :
    empiricalContinuationValue E N hN h data = EnvironmentStage.optimalValue
      ((empiricalStages E N hN data).drop (h.val + 1)) := by
  funext s
  exact EnvironmentStage.greedy_trajectoryValue _ s

/-- At the last decision stage the next-stage continuation is exactly zero. -/
theorem empiricalContinuationValue_terminal {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (hterminal : h.val + 1 = H) (data : Samples State Action H N) :
    empiricalContinuationValue E N hN h data = fun _ ↦ 0 := by
  have hd : (empiricalStages E N hN data).drop (h.val + 1) = [] := by
    apply List.drop_eq_nil_of_le
    rw [empiricalStages_length]
    omega
  funext s
  unfold empiricalContinuationValue
  rw [hd]
  exact DecisionStage.trajectoryValue_nil s

/-- A stage depends only on its own actual sample rows. -/
theorem empiricalStage_eq_of_data_eq {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data₁ data₂ : Samples State Action H N) (j : Fin H)
    (he : ∀ s a i, data₁ ((j,s,a),i) = data₂ ((j,s,a),i)) :
    empiricalStage E N hN data₁ j = empiricalStage E N hN data₂ j := by
  unfold empiricalStage
  congr 1
  funext s a
  congr 1
  funext i
  exact he s a i

/-- Equality of future samples gives literal equality of the chronological
empirical stage suffix, before any optimizer or value is selected. -/
theorem empiricalStages_drop_eq_of_future_eq {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (data₁ data₂ : Samples State Action H N)
    (he : ∀ j : Fin H, h < j → ∀ s a i, data₁ ((j,s,a),i) = data₂ ((j,s,a),i)) :
    (empiricalStages E N hN data₁).drop (h.val + 1) =
      (empiricalStages E N hN data₂).drop (h.val + 1) := by
  apply List.ext_getElem
  · simp [empiricalStages]
  · intro i hi hj
    simp only [empiricalStages, List.length_drop, List.length_ofFn] at hi hj
    have hidx : h.val + 1 + i < H := by omega
    simp only [empiricalStages, List.getElem_drop, List.getElem_ofFn]
    apply empiricalStage_eq_of_data_eq
    exact he ⟨h.val + 1 + i, hidx⟩ (by change h.val < h.val + 1 + i; omega)

/-- Fill all current/past observations with an arbitrary fixed state; retain
exactly the supplied strictly-future samples. -/
noncomputable def completeFutureData {H : ℕ} (h : Fin H) (N : ℕ) (x : State)
    (code : FutureCode (State := State) (Action := Action) h N) : Samples State Action H N :=
  fun i ↦ if hi : h < i.1.1 then code ⟨i, by simp [futureIndices, hi]⟩ else x

/-- The actual continuation value depends solely on the strictly-future code.
The reconstruction filler has no effect on any future stage. -/
theorem empiricalContinuationValue_factors_future {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (x : State) (data : Samples State Action H N) :
    empiricalContinuationValue E N hN h data =
      empiricalContinuationValue E N hN h (completeFutureData h N x (futureData h N data)) := by
  unfold empiricalContinuationValue
  rw [empiricalStages_drop_eq_of_future_eq E N hN h data
    (completeFutureData h N x (futureData h N data))]
  intro j hj s a i
  simp [completeFutureData, futureData, hj]

/-- Measurability is for the actual trajectory-valued optimal continuation,
under the finite discrete sample experiment. -/
theorem empiricalContinuationValue_measurable {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N) (h : Fin H) :
    Measurable (empiricalContinuationValue E N hN h) := measurable_of_countable _

/-- Genuine statistical independence of the actual empirical optimal
continuation value from the entire current stage/state/action sample row. -/
theorem empiricalContinuationValue_indep_row {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (s : State) (a : Action) :
    IndepFun (empiricalContinuationValue E N hN h)
      (fun data : Samples State Action H N ↦ fun i : Fin N ↦ data ((h,s,a),i))
      (samplingLaw E N) := by
  let x := Classical.choice (E h).state_nonempty
  let F : FutureCode (State := State) (Action := Action) h N → State → ℝ :=
    fun code ↦ empiricalContinuationValue E N hN h (completeFutureData h N x code)
  have hi := futureStatistic_indep_row E N h s a F
  have he : (fun data ↦ F (futureData h N data)) = empiricalContinuationValue E N hN h := by
    funext data
    exact (empiricalContinuationValue_factors_future E N hN h x data).symm
  rw [he] at hi
  exact hi

end StatisticalRL.FiniteHorizonGenerative
