import Formalization.ModelFree.TDSourceAccuracyExactSamples

/-! Theorem 4.1 (`thm:policy-evaluation-TD`,
`chapters/generative_model_model_free.tex:179–224`) for EVERY schedule pair `c₂ ≤ c₁` with
`c₁ c₂ ≤ 1/8`, not only `c₁ = c₂ = 1/4`: the existing component theorems already take the schedule
constants as arguments, so only the sample-budget constant `c₃` (depending on `c₁`, `c₂`) is
re-chosen. -/

open MeasureTheory
namespace StatisticalRL.TemporalDifference

local instance tdSourceGeneralScheduleStateMeasurable (State : Type*) :
    MeasurableSpace State := ⊤

/-- Terminal-accuracy theorem for arbitrary schedule constants `0 < c₂ ≤ c₁`, `c₁ c₂ ≤ 1/8`:
there is `c₃ > 0` (depending only on `c₁`, `c₂`) such that the source accuracy statement holds. -/
theorem tdSource_policyEvaluation_accuracy_exists_c₃ (c₁ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hcprod : c₁ * c₂ ≤ 1 / 8) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ)^3 *
        Real.log ((Fintype.card State : ℝ)*T/δ) /
          ((1-M.discount)^3*ε^2) ≤ T →
      1-δ ≤ (tdSamplingLaw M π T).real
        {data | ∀ s : State,
          |tdErrorValue M π η (tdSamplesExtend M T data) V₀ T s| ≤ ε} := by
  let c₃ : ℝ := max (max 4096 (Real.exp (1 / c₂) / Real.log 2 ^ 4))
    (max (4 / c₁) (1 / (c₁ * Real.log 2 ^ 2)))
  have hc₁ : 0 < c₁ := hc₂.trans_le hc₂₁
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 2 ^ 4 := pow_pos hlog2 4
  have hlog2sq : 0 < c₁ * Real.log 2 ^ 2 := by positivity
  have hc₃low : 4096 ≤ c₃ := (le_max_left _ _).trans (le_max_left _ _)
  have hc₃pos : 0 < c₃ := by linarith
  have hterminal : Real.exp (1 / c₂) ≤ c₃ * Real.log 2 ^ 4 :=
    (div_le_iff₀ hlog4).mp ((le_max_right _ _).trans (le_max_left _ _))
  have hc₁c₃ : (4 : ℝ) ≤ c₁ * c₃ := by
    have h : 4 / c₁ ≤ c₃ := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hc₁).mp h |>.trans_eq (mul_comm _ _)
  have hconstVariance : 1 ≤ c₁ * c₃ * Real.log 2 ^ 2 := by
    have h : 1 / (c₁ * Real.log 2 ^ 2) ≤ c₃ := (le_max_right _ _).trans (le_max_right _ _)
    have := (div_le_iff₀ hlog2sq).mp h
    nlinarith [this]
  refine ⟨c₃, hc₃pos, ?_⟩
  intro State Action instState instAction M π η δ ε T hγ hT
    hδ hδ1 hε hεmax hsource V₀ h₀ hbudget
  letI : Nonempty State := M.state_nonempty
  have hS : 1 ≤ Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hSreal : 1 ≤ (Fintype.card State : ℝ) := by exact_mod_cast hS
  have htime := tdSource_final_terminal_eligible_of_budget M c₂ c₃ ε δ T
    hT hc₂ hc₃pos hterminal hδ hδ1 hε hεmax hbudget
  have hstep : TDStepSizeSchedule M.discount c₁ c₂ T η := by
    simpa only [TDStepSizeSchedule, tdSourceRateSchedule] using hsource
  have hprod : c₁ * c₂ ≤ 1 / 8 := hcprod
  have hc₃large : (384 : ℝ) ≤ c₃ := le_trans (by norm_num) hc₃low
  have hc₃final : (3168 : ℝ) ≤ c₃ := le_trans (by norm_num) hc₃low
  have hfirst := tdSource_firstFreedman_allStates_of_budget M π η T T hT
    c₁ c₂ c₃ ε δ hc₁ hc₂ hc₁c₃ hprod
    hc₃large hγ hδ hδ1 hε hεmax hbudget hstep V₀ h₀ (le_rfl : T ≤ T) htime
  have hvarianceNorm := tdSource_varianceProxy_both_of_budget M π η T T hT
    c₁ c₂ c₃ ε δ hc₁ hc₂ hc₃large hprod
    hconstVariance hγ hδ hδ1 hε hεmax hbudget hsource V₀ h₀
    (le_rfl : T ≤ T) htime
  have hvariance : 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ‖tdSourceFixedTerminalProxyVector M π η T T V₀
            (tdSourceBarEta M.discount T) data‖ ≤
              16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
          ∀ s : State,
            tdTerminalVarianceSum M π η T T V₀ s data ≤
              33 * Real.log (T : ℝ) ^ 3 /
                ((1 - M.discount) ^ 3 * T)} := by
    let sourceEvent : Set (TDSamples State T) := {data |
      ‖tdSourceFixedTerminalProxyVector M π η T T V₀
          (tdSourceBarEta M.discount T) data‖ ≤
            16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
      ‖fun s => tdTerminalVarianceSum M π η T T V₀ s data‖ ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)}
    let targetEvent : Set (TDSamples State T) := {data |
      ‖tdSourceFixedTerminalProxyVector M π η T T V₀
          (tdSourceBarEta M.discount T) data‖ ≤
            16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
      ∀ s : State, tdTerminalVarianceSum M π η T T V₀ s data ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)}
    have hsubset : sourceEvent ⊆ targetEvent := by
      intro data hd
      refine ⟨hd.1, ?_⟩
      intro s
      have habs : |tdTerminalVarianceSum M π η T T V₀ s data| ≤
          33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T) := by
        have hn := (norm_le_pi_norm
          (fun q => tdTerminalVarianceSum M π η T T V₀ q data) s).trans hd.2
        simpa only [Real.norm_eq_abs] using hn
      exact (le_abs_self _).trans habs
    have hmono := ENNReal.toReal_mono
      (measure_ne_top (tdSamplingLaw M π T) targetEvent)
      (measure_mono hsubset)
    change 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real sourceEvent at hvarianceNorm
    change 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real targetEvent
    exact hvarianceNorm.trans hmono
  have hinitial := tdInitialError_contraction_of_source_budget M π η T T
    c₁ c₂ c₃ ε δ hT hc₁ hc₂ hc₃pos
    hconstVariance hδ hδ1 hε hεmax hstep hprod hbudget (le_rfl : T ≤ T)
    htime V₀ h₀
  have hfinal := tdSource_final_accuracy_of_events M π η T T c₃ ε δ
    (Fintype.card State : ℝ) V₀ hT (le_rfl : T ≤ T) hγ
    M.discount_lt_one hSreal rfl hδ hδ1 hε hεmax hc₃final hbudget
    hfirst hvariance hinitial
  exact hfinal

/-- Exact-`T` sampling form of `tdSource_policyEvaluation_accuracy_exists_c₃` (compare
`tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`). -/
theorem tdSource_policyEvaluation_exactSamples_accuracy_exists_c₃ (c₁ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hc₂₁ : c₂ ≤ c₁) (hcprod : c₁ * c₂ ≤ 1 / 8) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
      1 - δ ≤ (tdSourceSamplingLaw M π T).real
        {data | ∀ s : State,
          |tdSourceSampledIterate M π η T V₀ data s -
            M.trajectoryExpectedValue π s| ≤ ε} := by
  obtain ⟨c₃, hc₃, hmain⟩ := tdSource_policyEvaluation_accuracy_exists_c₃ c₁ c₂ hc₂ hc₂₁ hcprod
  refine ⟨c₃, hc₃, ?_⟩
  intro State Action _ _ M π η δ ε T hγ hT hδ hδone hε hεmax
    hη V₀ h₀ hbudget
  have hp := hmain State Action M π η δ ε T hγ hT hδ hδone
    hε hεmax hη V₀ h₀ hbudget
  let sourceGood : Set (TDSourceSamples State T) := {data | ∀ s : State,
    |tdSourceSampledIterate M π η T V₀ data s -
      M.trajectoryExpectedValue π s| ≤ ε}
  have hprojection : Measurable (tdUsedSampleProjection (State := State) T) :=
    measurable_of_countable _
  have hgood : MeasurableSet sourceGood := (Set.to_countable sourceGood).measurableSet
  have hprobability : (tdSourceSamplingLaw M π T).real sourceGood =
      (tdSamplingLaw M π T).real
        ((tdUsedSampleProjection T) ⁻¹' sourceGood) := by
    change ((tdSourceSamplingLaw M π T) sourceGood).toReal =
      ((tdSamplingLaw M π T) ((tdUsedSampleProjection T) ⁻¹' sourceGood)).toReal
    rw [← tdUsedSampleProjection_map_law M π T,
      Measure.map_apply hprojection hgood]
  change 1 - δ ≤ (tdSourceSamplingLaw M π T).real sourceGood
  rw [hprobability]
  refine hp.trans (measureReal_mono ?_)
  intro data hd
  change ∀ s : State,
    |tdSourceSampledIterate M π η T V₀ (tdUsedSampleProjection T data) s -
      M.trajectoryExpectedValue π s| ≤ ε
  intro s
  have hs := hd s
  change |tdSampledIterate M π η T V₀ data s -
    M.trajectoryExpectedValue π s| ≤ ε at hs
  rw [tdSampledIterate_eq_sourceSampledIterate M π η T V₀ data] at hs
  exact hs

end StatisticalRL.TemporalDifference
