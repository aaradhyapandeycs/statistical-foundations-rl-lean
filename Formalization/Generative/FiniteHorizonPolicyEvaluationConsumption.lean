import Formalization.Generative.FiniteHorizonBernsteinResidualBridge

import Formalization.Statements.Ch3Definitions
/-! Same-data actual trajectory consumption of the common auxiliary event.
The explicit cardinality/log factor is retained throughout. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance evaluationConsumptionStateMeasurable : MeasurableSpace State := ⊤

theorem trueAuxiliaryValueAt_zero_eq_policyTrajectorySuffix
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (h : ℕ) :
    trueAuxiliaryValueAt es f 0 h = policyTrajectorySuffix es f h := by
  funext s
  rw [policyTrajectorySuffix, EnvironmentStage.controlled_drop]
  exact trueAuxiliaryValue_zero_eq_trajectory _ _ _

theorem empiricalAuxiliaryValueAt_zero_eq_policyTrajectorySuffix {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) (f : ℕ → State → Action) (h : ℕ) :
    empiricalAuxiliaryValueAt E N hN data f 0 h =
      policyTrajectorySuffix (empiricalStages E N hN data) f h := by
  have hr : ∀ p ∈ (pairedEmpiricalStages E N hN data).drop h, p.2.reward = p.1.reward := by
    intro p hp
    have hp' : p ∈ pairedEmpiricalStages E N hN data := List.mem_of_mem_drop hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp'
    rw [← hi]
    rfl
  funext s
  have hh := comparisonAuxiliaryValue_zero_eq_trajectory
    ((pairedEmpiricalStages E N hN data).drop h) (fun k ↦ f (h + k)) hr s
  simpa only [empiricalAuxiliaryValueAt, comparisonAuxiliaryValueAt, policyTrajectorySuffix,
    EnvironmentStage.controlled_drop, List.map_drop, pairedEmpiricalStages_map_snd] using hh

/-- The same event supplies both actual evaluation errors at every start stage.
No second probability output is intersected, so the confidence is preserved. -/
theorem allLevelBernsteinEvent_policyEvaluation {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 12 * (H : ℝ) * allLevelBeta (H := H) State Action δ < N)
    (data : Samples State Action H N)
    (hevent : AllLevelBernsteinEvent E N hN fallback fixed δ data) (b : Bool) (h : ℕ) :
    ‖policyTrajectorySuffix (empiricalStages E N hN data)
        (sourceAuxiliaryPolicy E N hN fallback fixed b data) h -
      policyTrajectorySuffix (List.ofFn E)
        (sourceAuxiliaryPolicy E N hN fallback fixed b data) h‖ ≤
      6 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ)) := by
  have hh := auxiliaryErrorNormAt_le_lemmaNine (pairedEmpiricalStages E N hN data)
    (sourceAuxiliaryPolicy E N hN fallback fixed b data) H N
    (allLevelBeta (H := H) State Action δ) hH
    (allLevelBeta_nonneg E hH δ hδ hδ1)
    (by simp only [pairedEmpiricalStages, List.length_ofFn]; exact le_rfl) hsize
    (fun l hl ↦ allLevelBernsteinEvent_implies_residual E N hN hH fallback fixed δ hδ hδ1
      data hevent b l hl) h
  rw [pairedEmpiricalStages_map_fst] at hh
  change ‖empiricalAuxiliaryValueAt E N hN data
      (sourceAuxiliaryPolicy E N hN fallback fixed b data) 0 h -
    trueAuxiliaryValueAt (List.ofFn E) (sourceAuxiliaryPolicy E N hN fallback fixed b data) 0 h‖ ≤ _ at hh
  rwa [empiricalAuxiliaryValueAt_zero_eq_policyTrajectorySuffix,
    trueAuxiliaryValueAt_zero_eq_policyTrajectorySuffix] at hh

/-- An actual-law two-policy all-stage evaluation guarantee with the explicit
safe logarithm; no confidence/log absorption is hidden. -/
theorem simultaneous_policyEvaluation_probability {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 12 * (H : ℝ) * allLevelBeta (H := H) State Action δ < N) :
    1 - δ < (samplingLaw E N).real {data | ∀ (b : Bool) (h : ℕ),
      ‖policyTrajectorySuffix (empiricalStages E N hN data)
          (sourceAuxiliaryPolicy E N hN fallback fixed b data) h -
        policyTrajectorySuffix (List.ofFn E)
          (sourceAuxiliaryPolicy E N hN fallback fixed b data) h‖ ≤
        6 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))} := by
  have hp := allLevelBernsteinEvent_probability E N hN hH fallback fixed δ hδ hδ1
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top (samplingLaw E N) _)
  intro data hd b h
  exact allLevelBernsteinEvent_policyEvaluation E N hN hH fallback fixed δ hδ hδ1 hsize data hd b h

end StatisticalRL.FiniteHorizonGenerative
