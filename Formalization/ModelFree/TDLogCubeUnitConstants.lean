import Formalization.ModelFree.TDSourceFullAccuracyUniversal
import Formalization.ModelFree.TDSourceSamplingProjection

/-! transport of the existing TD accuracy layers to the log³ step-size schedule
`eq:thm:infinite-horizaon-eta` (`chapters/generative_model_model_free.tex:881–886`) with
constants c₁ = c₂ = 1, by instantiating the log² TD-layer constants at
c₁' = c₂' = 1 / log T and c₃' = 8192 · log T. At the only terminal used (t = T) the
eligibility premise `T / (c₂' log T) ≤ T` is `T ≤ T`; it is supplied directly. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

local instance tdLogCubeStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- The log³ rate with constant 1 is the log² rate with constant 1/log T. -/
theorem td_logCube_rate_eq (γ : ℝ) (T i : ℕ) (hL : Real.log (T : ℝ) ≠ 0) :
    (1 / Real.log (T : ℝ)) * (1 - γ) * (i : ℝ) / Real.log (T : ℝ) ^ 2 =
      1 * (1 - γ) * (i : ℝ) / Real.log (T : ℝ) ^ 3 := by
  field_simp

/-- TD accuracy on the padded sampling law under the log³ schedule with constants 1,
budget `8192 log⁴T log(ST/δ) / ((1−γ)³ε²) ≤ T`. -/
theorem td_logCube_unitConstants_accuracy
    {State Action : Type*} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ)
    (hγ : 1 / 2 ≤ M.discount) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T →
      1 / (1 + 1 * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η i ∧
        η i ≤ 1 / (1 + 1 * (1 - M.discount) * i / Real.log (T : ℝ) ^ 3))
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hbudget : 8192 * Real.log (T : ℝ) ^ 4 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ T) :
    1 - δ ≤ (tdSamplingLaw M π T).real
      {data | ∀ s : State,
        |tdErrorValue M π η (tdSamplesExtend M T data) V₀ T s| ≤ ε} := by
  letI : Nonempty State := M.state_nonempty
  set L : ℝ := Real.log (T : ℝ) with hLdef
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := hLpos.ne'
  let c' : ℝ := 1 / L
  let c₃ : ℝ := 8192 * L
  have hc' : 0 < c' := by positivity
  have hc₃pos : 0 < c₃ := by positivity
  have hc'c₃ : c' * c₃ = 8192 := by
    simp only [c', c₃]; field_simp
  have hc₃large : (3168 : ℝ) ≤ c₃ := by simp only [c₃]; linarith
  have hc₃384 : (384 : ℝ) ≤ c₃ := le_trans (by norm_num) hc₃large
  have hc₁c₃ : (4 : ℝ) ≤ c' * c₃ := by rw [hc'c₃]; norm_num
  have hconstVariance : 1 ≤ c' * c₃ * Real.log 2 ^ 2 := by
    rw [hc'c₃]
    have hsq : (1/4 : ℝ) ≤ Real.log 2 ^ 2 :=
      calc (1/4 : ℝ) = (1/2) ^ 2 := by norm_num
        _ ≤ Real.log 2 ^ 2 := pow_le_pow_left₀ (by norm_num) hlog2 2
    linarith
  have hbudget' : c₃ * L ^ 3 * Real.log ((Fintype.card State : ℝ) * T / δ) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ T := by
    have he : c₃ * L ^ 3 = 8192 * L ^ 4 := by simp only [c₃]; ring
    rw [he]; exact hbudget
  have hS : 1 ≤ Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hεmax' : ε ≤ 1 / (1 - M.discount) := by
    simpa [DiscountedMDP.effectiveHorizon] using hεmax
  have hnorm := td_mainBudget_implies_normalized c₃ M.discount δ ε
    (Fintype.card State) T hc₃pos hS hT M.discount_lt_one hδ hδ1 hε hεmax' hbudget'
  -- 8192 L⁵ ≤ T(1-γ) ≤ T, so T ≥ 256, so L ≥ 8 log 2 ≥ 4.
  have hgap : 0 ≤ 1 - M.discount := sub_nonneg.mpr M.discount_lt_one.le
  have hgap1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hTr : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hT256 : (256 : ℝ) ≤ T := by
    have h5 : (1 / 2 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    have hle : c₃ * L ^ 4 ≤ T := hnorm.trans (by
      have := mul_le_mul_of_nonneg_left hgap1 hTr.le
      linarith)
    have he : c₃ * L ^ 4 = 8192 * L ^ 5 := by simp only [c₃]; ring
    rw [he] at hle
    linarith
  have hL4 : (4 : ℝ) ≤ L := by
    have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have hl := Real.log_le_log (by norm_num) hT256
    rw [h256] at hl
    linarith
  have hprod : c' * c' ≤ 1 / 8 := by
    simp only [c']
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul hL4 hL4 (by norm_num) (by linarith)
    linarith
  have hsource : tdSourceRateSchedule M.discount c' c' T η := by
    intro i hi hiT
    have h := hη i hi hiT
    simp only [c']
    rw [td_logCube_rate_eq M.discount T T hLne, td_logCube_rate_eq M.discount T i hLne]
    exact h
  have hstep : TDStepSizeSchedule M.discount c' c' T η := by
    simpa only [TDStepSizeSchedule, tdSourceRateSchedule] using hsource
  have htime : (T : ℝ) / (c' * L) ≤ T := by
    have : c' * L = 1 := by simp only [c']; field_simp
    rw [this, div_one]
  have hSreal : 1 ≤ (Fintype.card State : ℝ) := by exact_mod_cast hS
  have hfirst := tdSource_firstFreedman_allStates_of_budget M π η T T hT
    c' c' c₃ ε δ hc' hc' hc₁c₃ hprod hc₃384 hγ hδ hδ1 hε hεmax hbudget' hstep V₀ h₀
    (le_rfl : T ≤ T) htime
  have hvarianceNorm := tdSource_varianceProxy_both_of_budget M π η T T hT
    c' c' c₃ ε δ hc' hc' hc₃384 hprod hconstVariance hγ hδ hδ1 hε hεmax hbudget'
    hsource V₀ h₀ (le_rfl : T ≤ T) htime
  have hvariance : 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ‖tdSourceFixedTerminalProxyVector M π η T T V₀
            (tdSourceBarEta M.discount T) data‖ ≤
              16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
          ∀ s : State,
            tdTerminalVarianceSum M π η T T V₀ s data ≤
              33 * Real.log (T : ℝ) ^ 3 /
                ((1 - M.discount) ^ 3 * T)} := by
    refine hvarianceNorm.trans (measureReal_mono ?_)
    intro data hd
    refine ⟨hd.1, fun s ↦ ?_⟩
    have hn := (norm_le_pi_norm
      (fun q => tdTerminalVarianceSum M π η T T V₀ q data) s).trans hd.2
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)
  have hinitial := tdInitialError_contraction_of_source_budget M π η T T
    c' c' c₃ ε δ hT hc' hc' hc₃pos hconstVariance hδ hδ1 hε hεmax hstep hprod
    hbudget' (le_rfl : T ≤ T) htime V₀ h₀
  exact tdSource_final_accuracy_of_events M π η T T c₃ ε δ
    (Fintype.card State : ℝ) V₀ hT (le_rfl : T ≤ T) hγ
    M.discount_lt_one hSreal rfl hδ hδ1 hε hεmax hc₃large hbudget'
    hfirst hvariance hinitial

/-- The same accuracy on the exact-T sampling experiment (time-zero layer dropped
through `tdUsedSampleProjection_map_law`, the `Fin.succ` marginal). -/
theorem tdSource_logCube_unitConstants_exactSamples_accuracy
    {State Action : Type*} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ)
    (hγ : 1 / 2 ≤ M.discount) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → i ≤ T →
      1 / (1 + 1 * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η i ∧
        η i ≤ 1 / (1 + 1 * (1 - M.discount) * i / Real.log (T : ℝ) ^ 3))
    (V₀ : State → ℝ) (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hbudget : 8192 * Real.log (T : ℝ) ^ 4 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ T) :
    1 - δ ≤ (tdSourceSamplingLaw M π T).real
      {data | ∀ s : State,
        |tdSourceSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s| ≤ ε} := by
  have hp := td_logCube_unitConstants_accuracy M π η δ ε T hγ hT hδ hδ1 hε hεmax hη V₀ h₀
    hbudget
  let sourceGood : Set (TDSourceSamples State T) := {data | ∀ s : State,
    |tdSourceSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s| ≤ ε}
  have hprojection : Measurable (tdUsedSampleProjection (State := State) T) :=
    measurable_of_countable _
  have hgood : MeasurableSet sourceGood := (Set.to_countable sourceGood).measurableSet
  have hprobability : (tdSourceSamplingLaw M π T).real sourceGood =
      (tdSamplingLaw M π T).real ((tdUsedSampleProjection T) ⁻¹' sourceGood) := by
    change ((tdSourceSamplingLaw M π T) sourceGood).toReal =
      ((tdSamplingLaw M π T) ((tdUsedSampleProjection T) ⁻¹' sourceGood)).toReal
    rw [← tdUsedSampleProjection_map_law M π T, Measure.map_apply hprojection hgood]
  change 1 - δ ≤ (tdSourceSamplingLaw M π T).real sourceGood
  rw [hprobability]
  refine hp.trans (measureReal_mono ?_)
  intro data hd s
  have hs := hd s
  change |tdSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s| ≤ ε at hs
  rw [tdSampledIterate_eq_sourceSampledIterate M π η T V₀ data] at hs
  exact hs

end StatisticalRL.TemporalDifference
