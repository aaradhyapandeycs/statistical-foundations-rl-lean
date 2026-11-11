import Formalization.ModelFree.TDSourceFirstFreedmanAssembly
import Formalization.ModelFree.TDOriginalVarianceScale
import Formalization.ModelFree.TDInitialErrorContraction
import Formalization.ModelFree.TDActualErrorUnroll
import Formalization.ModelFree.TDSourceFinalScalarBudgetConsumer
import Formalization.ModelFree.TDSourceFixedTerminalProxyBudget
import Formalization.ModelFree.TDVarianceSum

set_option maxHeartbeats 500000

/-! Compose the fixed-terminal first-Freedman event, variance conclusions, and
deterministic initial-error bound through the actual error unrolling. The
probabilistic and almost-everywhere ingredients remain explicit premises, and
the scalar absorption uses a stated sufficient relation among source
constants. This helper does not close the source theorem by itself. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance tdSourceFinalCompositionStateMeasurable : MeasurableSpace State := ⊤

/-- The exact final source terminal `t=T` is eligible under the printed
budget, with the source-specific universal-constant relation made explicit.
This keeps eligibility out of an unproved final-interface premise. -/
theorem tdSource_final_terminal_eligible_of_budget
    (M : DiscountedMDP State Action) (c₂ c₃ ε δ : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hconstants : Real.exp (1 / c₂) ≤ c₃ * Real.log 2 ^ 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεmax : ε ≤ M.effectiveHorizon)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ)) :
    (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ T := by
  letI : Nonempty State := M.state_nonempty
  have hS : 1 ≤ Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hnormalized := td_mainBudget_implies_normalized c₃ M.discount δ ε
    (Fintype.card State) T hc₃ hS hT M.discount_lt_one hδ hδ1 hε hεmax hBudget
  have hlate := td_normalizedBudget_implies_final_late M.discount c₂ c₃ T
    hT M.discount_nonneg M.discount_lt_one hc₂ hc₃ hconstants hnormalized
  exact td_final_terminal_is_late c₂ T hT hc₂ hlate

/-- Combine same-terminal events under the actual finite TD sampling law.
The first-Freedman event, the joint proxy/original-variance event, and the
deterministic initial-error estimate are explicit premises. The output is a
probability-`1−δ` actual-policy value error bound; the source-side premises
are not proved by this wrapper. -/
theorem tdSource_final_accuracy_of_events
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (c₃ ε δ : ℝ) (S : ℝ)
    (V₀ : State → ℝ)
    (hT : 2 ≤ T) (ht : t ≤ T)
    (hγhalf : 1 / 2 ≤ M.discount) (hγ1 : M.discount < 1)
    (hS : 1 ≤ S) (hScard : S = (Fintype.card State : ℝ))
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεH : ε ≤ M.effectiveHorizon)
    (hc₃ : 3168 ≤ c₃)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (S * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ))
    (hFirst : 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ∀ s : State,
          |∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
            Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
              ((3 * Real.log (T : ℝ) ^ 3 /
                ((1 - M.discount) ^ 4 * T)) /
                (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) *
                (3 * Real.log (S * T / δ))) +
            (4 / 3) * (4 * M.discount * Real.log (T : ℝ) ^ 3 /
              ((1 - M.discount) ^ 2 * T)) *
              (3 * Real.log (S * T / δ))})
    (hVariance : 1 - δ / (2 * (T : ℝ)) ≤
      (tdSamplingLaw M π T).real
        {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀
            (tdSourceBarEta M.discount T) data‖ ≤
              16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
          ∀ s : State,
            tdTerminalVarianceSum M π η T t V₀ s data ≤
              33 * Real.log (T : ℝ) ^ 3 /
                ((1 - M.discount) ^ 3 * T)})
    (hInitial : ‖tdErrorPropagate M π η 0 t
        (V₀ - M.trajectoryExpectedValue π)‖ ≤
          M.effectiveHorizon / (T : ℝ) ^ 2) :
    1 - δ ≤ (tdSamplingLaw M π T).real
      {data | ∀ s : State,
        |tdErrorValue M π η (tdSamplesExtend M T data) V₀ t s| ≤ ε} := by
  classical
  let H : ℝ := M.effectiveHorizon
  let μ : Measure (TDSamples State T) := tdSamplingLaw M π T
  let firstGood : Set (TDSamples State T) := {data | ∀ s : State,
    |∑ k ∈ Finset.Icc 1 t,
      tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
      Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
        ((3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 4 * T)) /
          (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) *
          (3 * Real.log (S * T / δ))) +
        (4 / 3) * (4 * M.discount * Real.log (T : ℝ) ^ 3 /
          ((1 - M.discount) ^ 2 * T)) * (3 * Real.log (S * T / δ))}
  let varianceGood : Set (TDSamples State T) := {data |
    ‖tdSourceFixedTerminalProxyVector M π η T t V₀
        (tdSourceBarEta M.discount T) data‖ ≤
          16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2 ∧
    ∀ s : State,
      tdTerminalVarianceSum M π η T t V₀ s data ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T)}
  let badUnion : Set (TDSamples State T) := firstGoodᶜ ∪ varianceGoodᶜ
  have hgap : 0 < 1 - M.discount := sub_pos.mpr hγ1
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hH : H = 1 / (1 - M.discount) := by
    simp [H, DiscountedMDP.effectiveHorizon]
  have hBudgetCard : c₃ * Real.log (T : ℝ) ^ 3 *
      Real.log ((Fintype.card State : ℝ) * T / δ) /
        ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) := by
    simpa [hScard] using hBudget
  have hBudgetScalar : c₃ * Real.log (T : ℝ) ^ 3 *
      Real.log (S * T / δ) / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) := by
    simpa [hScard] using hBudgetCard
  have hHge2 : 2 ≤ H := by
    rw [hH]
    rw [le_div_iff₀ hgap]
    linarith
  have hfloor :
      ((3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 4 * T)) /
        (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) ≤
      33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T) := by
    have hfloor' := tdSource_firstFreedman_floor_le M.discount T hT hγhalf hγ1
    have hscale : 3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 2 * T) ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T) := by
      have hgapLe : 1 - M.discount ≤ 1 := by linarith
      have hlog0 : 0 ≤ Real.log (T : ℝ) :=
        (Real.log_pos (by exact_mod_cast (by omega : 1 < T))).le
      have hnum : 0 ≤ 3 * Real.log (T : ℝ) ^ 3 := by positivity
      have hden₁ : 0 < (1 - M.discount) ^ 2 * T := by positivity
      have hden₂ : 0 < (1 - M.discount) ^ 3 * T := by positivity
      rw [div_le_div_iff₀ hden₁ hden₂]
      nlinarith [mul_le_mul_of_nonneg_left hgapLe
        (mul_nonneg hnum (by positivity : 0 ≤ (1 - M.discount) ^ 2 * T))]
    exact hfloor'.trans hscale
  have hscalar := tdSource_final_scalar_absorption M.discount H ε δ S c₃ T
    hγhalf hγ1 hH hHge2 hT hS hδ hδ1 hε hεH hc₃ hBudgetScalar
  have hrootBound := hscalar.1
  have hlinearBound := hscalar.2.1
  have hinitialSmall : M.effectiveHorizon / (T : ℝ) ^ 2 ≤ ε / 4 := by
    simpa [H] using hscalar.2.2
  have hpointwise (data : TDSamples State T) (hF : data ∈ firstGood)
      (hV : data ∈ varianceGood) (s : State) :
      |tdErrorValue M π η (tdSamplesExtend M T data) V₀ t s| ≤ ε := by
    have hF' := hF s
    have hW := hV.2 s
    have hmax : max (tdTerminalVarianceSum M π η T t V₀ s data)
        ((3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 4 * T)) /
          (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) ≤
        33 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 3 * T) :=
      max_le hW hfloor
    have hrootArg :
        8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
            ((3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 4 * T)) /
              (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) *
            (3 * Real.log (S * T / δ)) ≤
          8 * (33 * Real.log (T : ℝ) ^ 3 /
            ((1 - M.discount) ^ 3 * T)) * (3 * Real.log (S * T / δ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hmax (by norm_num)
      · have hlogq : 0 ≤ Real.log (S * T / δ) := by
          apply Real.log_nonneg
          have hST : 2 ≤ S * (T : ℝ) := by
            have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
            nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : 0 ≤ (T : ℝ))]
          rw [one_le_div hδ]
          nlinarith [hST, hδ1]
        positivity
    have hroot : Real.sqrt
        (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
          ((3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 4 * T)) /
            (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) *
          (3 * Real.log (S * T / δ))) ≤ ε / 2 := by
      exact (Real.sqrt_le_sqrt hrootArg).trans hrootBound
    have hrad :
        Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
          ((3 * Real.log (T : ℝ) ^ 3 / ((1 - M.discount) ^ 4 * T)) /
            (2 : ℝ) ^ tdSourceFreedmanLevel M.discount) *
          (3 * Real.log (S * T / δ))) +
        (4 / 3) * (4 * M.discount * Real.log (T : ℝ) ^ 3 /
          ((1 - M.discount) ^ 2 * T)) * (3 * Real.log (S * T / δ)) ≤
        3 * ε / 4 := by linarith [hroot, hlinearBound]
    have hsumEq :
        (∑ k ∈ Finset.Icc 1 t,
          tdWeightedErrorIncrement M π η (tdSamplesExtend M T data) V₀ t k) s =
        ∑ k ∈ Finset.Icc 1 t,
          tdSampledWeightedIncrement M π η T t k V₀ s data := by
      simp [tdSampledWeightedIncrement, Finset.sum_apply]
    have hunroll := congrFun
      (tdErrorValue_eq_initial_add_increments M π η
        (tdSamplesExtend M T data) V₀ t) s
    have hunroll' : tdErrorValue M π η (tdSamplesExtend M T data) V₀ t s =
        tdErrorPropagate M π η 0 t (V₀ - M.trajectoryExpectedValue π) s +
          ∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η T t k V₀ s data := by
      calc
        _ = (tdErrorPropagate M π η 0 t
            (V₀ - M.trajectoryExpectedValue π) +
            ∑ k ∈ Finset.Icc 1 t,
              tdWeightedErrorIncrement M π η (tdSamplesExtend M T data) V₀ t k) s := hunroll
        _ = tdErrorPropagate M π η 0 t
              (V₀ - M.trajectoryExpectedValue π) s +
            (∑ k ∈ Finset.Icc 1 t,
              tdWeightedErrorIncrement M π η (tdSamplesExtend M T data) V₀ t k) s := by rfl
        _ = _ := by rw [hsumEq]
    calc
      |tdErrorValue M π η (tdSamplesExtend M T data) V₀ t s| ≤
          |tdErrorPropagate M π η 0 t
            (V₀ - M.trajectoryExpectedValue π) s| +
          |∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η T t k V₀ s data| := by
              rw [hunroll']
              exact abs_add_le _ _
      _ ≤ M.effectiveHorizon / (T : ℝ) ^ 2 + 3 * ε / 4 := by
        apply add_le_add
        · have hcoord := (norm_le_pi_norm
            (tdErrorPropagate M π η 0 t
              (V₀ - M.trajectoryExpectedValue π)) s).trans hInitial
          simpa only [Real.norm_eq_abs] using hcoord
        · exact hF'.trans hrad
      _ ≤ ε := by linarith [hinitialSmall]
  have hbadFirst : μ.real firstGoodᶜ ≤ δ / (2 * (T : ℝ)) := by
    have hc := measureReal_compl (μ := μ)
      ((Set.to_countable firstGood).measurableSet)
    rw [probReal_univ] at hc
    change 1 - δ / (2 * (T : ℝ)) ≤ μ.real firstGood at hFirst
    linarith
  have hbadVariance : μ.real varianceGoodᶜ ≤ δ / (2 * (T : ℝ)) := by
    have hc := measureReal_compl (μ := μ)
      ((Set.to_countable varianceGood).measurableSet)
    rw [probReal_univ] at hc
    change 1 - δ / (2 * (T : ℝ)) ≤ μ.real varianceGood at hVariance
    linarith
  have hbadUnion : μ.real badUnion ≤ δ / (T : ℝ) := by
    calc
      _ ≤ μ.real firstGoodᶜ + μ.real varianceGoodᶜ :=
        measureReal_union_le (μ := μ) firstGoodᶜ varianceGoodᶜ
      _ ≤ δ / (2 * (T : ℝ)) + δ / (2 * (T : ℝ)) :=
        add_le_add hbadFirst hbadVariance
      _ = δ / (T : ℝ) := by ring
  let accuracy : Set (TDSamples State T) := {data | ∀ s : State,
    |tdErrorValue M π η (tdSamplesExtend M T data) V₀ t s| ≤ ε}
  have hsubset : badUnionᶜ ⊆ accuracy := by
    intro data hgood s
    have hgoodFirst : data ∈ firstGood := by
      by_contra hn
      exact hgood (Or.inl hn)
    have hgoodVariance : data ∈ varianceGood := by
      by_contra hn
      exact hgood (Or.inr hn)
    exact hpointwise data hgoodFirst hgoodVariance s
  have hmeasure := measureReal_mono hsubset (measure_ne_top μ accuracy)
  have hcompl := measureReal_compl (μ := μ)
    ((Set.to_countable badUnion).measurableSet)
  rw [probReal_univ] at hcompl
  have hTge1 : 1 ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  have hfrac : δ / (T : ℝ) ≤ δ := by
    apply (div_le_iff₀ hTpos).2
    calc
      δ = δ * 1 := by ring
      _ ≤ δ * (T : ℝ) := mul_le_mul_of_nonneg_left hTge1 hδ.le
  change 1 - δ ≤ μ.real accuracy
  have hgoodProb : 1 - δ / (T : ℝ) ≤ μ.real badUnionᶜ := by
    linarith [hcompl, hbadUnion]
  have hmono : μ.real badUnionᶜ ≤ μ.real accuracy :=
    ENNReal.toReal_mono (measure_ne_top μ accuracy) (measure_mono hsubset)
  linarith

end StatisticalRL.TemporalDifference
