import Formalization.Generative.FiniteHorizonSampleArithmetic

/-! Pathwise one-stage endpoint; no concentration or sample threshold is needed. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem auxiliaryResidualCondition_of_length_le_one
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (a b : ℝ) (hlen : pairs.length ≤ 1) :
    auxiliaryResidualCondition pairs f l a b := by
  cases pairs with
  | nil => trivial
  | cons p tail =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
    subst tail
    rcases p with ⟨E,F⟩
    constructor
    · intro s
      simp [auxiliaryPolicyReward, trueAuxiliaryValue, policyRowResidual]
      change 0 ≤ b * ‖(0 : State → ℝ)‖
      simp
    · trivial

/-- With only one reward stage, every fixed or selected policy has identical
true and empirical actual trajectory values, since the reward is known. -/
theorem oneStage_policyTrajectorySuffix_eq
    (E : Fin 1 → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action 1 N) (f : ℕ → State → Action) (h : ℕ) :
    policyTrajectorySuffix (empiricalStages E N hN data) f h =
      policyTrajectorySuffix (List.ofFn E) f h := by
  have hlen : (pairedEmpiricalStages E N hN data).length ≤ 1 := by simp [pairedEmpiricalStages]
  have hh := auxiliaryErrorNormAt_le_lemmaNine (pairedEmpiricalStages E N hN data) f 1 N 0
    (by decide) le_rfl hlen (by simpa using (Nat.cast_pos.mpr hN : (0 : ℝ) < N))
    (by
      intro l hl
      simpa using (auxiliaryResidualCondition_of_length_le_one
        (pairedEmpiricalStages E N hN data) f l 0 0 hlen)) h
  rw [pairedEmpiricalStages_map_fst] at hh
  change ‖empiricalAuxiliaryValueAt E N hN data f 0 h -
    trueAuxiliaryValueAt (List.ofFn E) f 0 h‖ ≤ _ at hh
  rw [empiricalAuxiliaryValueAt_zero_eq_policyTrajectorySuffix,
    trueAuxiliaryValueAt_zero_eq_policyTrajectorySuffix] at hh
  have hz : ‖policyTrajectorySuffix (empiricalStages E N hN data) f h -
      policyTrajectorySuffix (List.ofFn E) f h‖ = 0 := by
    apply le_antisymm
    · simpa using hh
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- One-stage planning is exactly optimal for V and forced-action Q, for every
sample outcome, even when the logarithmic sample threshold is arbitrarily small. -/
theorem oneStage_causalPolicyPerformance
    (E : Fin 1 → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (data : Samples State Action 1 N) :
    CausalPolicyPerformanceEvent E N hN fallback 0 data := by
  let f := backwardGreedyActions fallback (empiricalStages E N hN data)
  let fixed := backwardGreedyActions fallback (List.ofFn E)
  have hv (h : ℕ) (s : State) :
      0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s - policyTrajectorySuffix (List.ofFn E) f h s ∧
      EnvironmentStage.optimalValue ((List.ofFn E).drop h) s - policyTrajectorySuffix (List.ofFn E) f h s ≤ 0 := by
    have hop := policyTrajectorySuffix_le_optimal (empiricalStages E N hN data) fixed h s
    have hetrue := congrFun (oneStage_policyTrajectorySuffix_eq E N hN data fixed h) s
    have hefit := congrFun (oneStage_policyTrajectorySuffix_eq E N hN data f h) s
    have htrue := congrFun (backwardGreedyActions_policyTrajectorySuffix fallback (List.ofFn E) h) s
    have hfit := congrFun (backwardGreedyActions_policyTrajectorySuffix fallback (empiricalStages E N hN data) h) s
    change policyTrajectorySuffix (List.ofFn E) fixed h s = _ at htrue
    change policyTrajectorySuffix (empiricalStages E N hN data) f h s = _ at hfit
    refine ⟨sub_nonneg.mpr (policyTrajectorySuffix_le_optimal _ f h s), ?_⟩
    linarith
  dsimp only [CausalPolicyPerformanceEvent]
  intro h
  exact ⟨hv h, fun s a ↦ policyTrajectoryQSuffix_loss_le_of_values (List.ofFn E) f 0 le_rfl
    (fun k t ↦ (hv k t).2) h s a⟩

/-- Weakening a simultaneous V/Q radius retains both lower and upper bounds. -/
theorem causalPolicyPerformanceEvent_mono {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (R S : ℝ) (hRS : R ≤ S) (data : Samples State Action H N)
    (he : CausalPolicyPerformanceEvent E N hN fallback R data) :
    CausalPolicyPerformanceEvent E N hN fallback S data := by
  dsimp only [CausalPolicyPerformanceEvent]
  intro h
  exact ⟨fun s ↦ ⟨(he h).1 s |>.1, ((he h).1 s).2.trans hRS⟩,
    fun s a ↦ ⟨((he h).2 s a).1, ((he h).2 s a).2.trans hRS⟩⟩

end StatisticalRL.FiniteHorizonGenerative
