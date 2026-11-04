import Formalization.ModelFree.TDSourceFixedTerminalProxyDefinitions
import Formalization.ModelFree.TDSourceFixedTerminalProxy
import Formalization.ModelFree.TDSourceRateProxyTransport
import Formalization.ModelFree.TDSourceFreedmanBudgetSmallness
import Formalization.ModelFree.TDSourceFreedmanLogComparison
import Formalization.ModelFree.TDSourceFreedmanDyadicCutoff

/-!

Instantiate the fixed-terminal all-state second-Freedman event from the finite source schedule and sample budget, transport through the zero-tail extension, and state the result as an explicit infinity-norm event.
-/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSourceFixedTerminalBudgetStateMeasurable : MeasurableSpace State := ⊤

/-- Exact source-schedule fixed-terminal proxy bound, in the infinity norm.
The proof derives unit rates, the late-rate envelope and per-coordinate
smallness from the finite schedule and main sample budget, extends rates by
zero past T, applies the actual sampling-law result, and transports the event
back. The source terminal eligibility condition remains explicit. -/
theorem tdSource_fixedTerminalProxy_of_budget
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (hT : 2 ≤ T)
    (c₁ c₂ c₃ ε δ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 384 ≤ c₃)
    (hγhalf : 1 / 2 ≤ M.discount)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεmax : ε ≤ M.effectiveHorizon)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ))
    (hSched : tdSourceRateSchedule M.discount c₁ c₂ T η)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (ht : t ≤ T)
    (helig : tdSourceEligibleTerminal T c₂ t) :
    1 - δ / (2 * T) ≤ (tdSamplingLaw M π T).real
      {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀
          (tdSourceBarEta M.discount T) data‖ ≤
        16 * tdSourceBarEta M.discount T * M.effectiveHorizon ^ 2} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let S : ℝ := Fintype.card State
  let K : ℕ := tdSourceFreedmanLevel M.discount
  let barη : ℝ := tdSourceBarEta M.discount T
  let ηext : ℕ → ℝ := tdSourceRateExtend T η
  have hγ1 : M.discount < 1 := M.discount_lt_one
  have hS : 1 ≤ S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hK : 0 < K := by
    dsimp [K, tdSourceFreedmanLevel]
    have hgap : 0 < 1 - M.discount := by linarith
    have hHge2 : 2 ≤ 1 / (1 - M.discount) := by
      rw [le_div_iff₀ hgap]
      linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hceil : 0 < Nat.ceil
        (Real.log (1 / (1 - M.discount)) / Real.log 2) := by
      apply Nat.ceil_pos.mpr
      apply div_pos
      · apply Real.log_pos
        exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hHge2
      · exact hlog2
    omega
  have hKsq := tdSourceFreedmanLevel_covers_effectiveHorizon_sq
    M.discount hγhalf hγ1
  have hHge1 : 1 ≤ M.effectiveHorizon := by
    rw [DiscountedMDP.effectiveHorizon, le_div_iff₀ (sub_pos.mpr hγ1)]
    linarith
  have hHleSq : M.effectiveHorizon ≤ M.effectiveHorizon ^ 2 := by
    calc
      M.effectiveHorizon = M.effectiveHorizon * 1 := by ring
      _ ≤ M.effectiveHorizon * M.effectiveHorizon :=
        mul_le_mul_of_nonneg_left hHge1 M.effectiveHorizon_nonneg
      _ = M.effectiveHorizon ^ 2 := by rw [pow_two]
  have hKcut : M.effectiveHorizon ≤ (2 : ℝ) ^ K := by
    change M.effectiveHorizon ≤ (2 : ℝ) ^ tdSourceFreedmanLevel M.discount
    exact hHleSq.trans (by simpa [DiscountedMDP.effectiveHorizon] using hKsq)
  have hlogBound := tdSourceBudget_logComparison M.discount c₃ ε δ S T hT
    hγhalf hγ1 hc₃ hδ hδ1 hS hε hεmax hBudget
  have hsmallness := tdSourceBudget_to_barEta_smallness M.discount c₃ ε δ S T K
    hT hγhalf hγ1 hc₃ hδ hδ1 hS hε hεmax hK hBudget hlogBound
  have hbar0 : 0 ≤ barη := by simpa [barη, tdSourceBarEta] using hsmallness.1
  have hbarHalf : barη ≤ 1 / 2 := by
    simpa [barη, tdSourceBarEta] using hsmallness.2.1
  have hsmall : barη * Real.log
      (2 * K / (δ / (2 * S * T))) ≤ 1 / 64 := by
    simpa [barη, tdSourceBarEta, S, K] using hsmallness.2.2
  have hfinite : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1 :=
    tdSourceRateSchedule_unit_interval M.discount c₁ c₂ T hT hγ1 hc₁ hc₂ η hSched
  have hηext : ∀ i, 1 ≤ i → 0 ≤ ηext i ∧ ηext i ≤ 1 := by
    simpa [ηext] using tdSourceRateExtend_unit_interval T η hfinite
  have hbarExt : ∀ k, t / 2 + 1 ≤ k → k ≤ t → ηext k ≤ barη := by
    intro k hlate hkt
    have hrate := tdSourceRateSchedule_eligible_late_le
      M.discount c₁ c₂ T t k hT ht hγ1 hc₂ η hSched helig hlate hkt
    have hkT : k ≤ T := hkt.trans ht
    have hext : ηext k = η k := by simp [ηext, tdSourceRateExtend, hkT]
    rw [hext]
    simpa [barη, tdSourceBarEta] using hrate
  have hfixed := tdSquareLateWindowProxy_fixedTerminal_allStates
    M π ηext T t hT ht c₂ hc₂ helig V₀ h₀ hηext barη hbar0 hbarHalf
    hbarExt K hK hKcut δ hδ hδ1 hsmall
  have hfixedCoord : 1 - δ / (2 * T) ≤ (tdSamplingLaw M π T).real
      {data | ∀ q : State,
        tdSquareLateWindowRandomProxy M π ηext T t V₀ barη q data ≤
          16 * barη * M.effectiveHorizon ^ 2} := by
    simpa [barη] using hfixed
  have htransport : {data | ∀ q : State,
      tdSquareLateWindowRandomProxy M π ηext T t V₀ barη q data ≤
        16 * barη * M.effectiveHorizon ^ 2} =
      {data | ∀ q : State,
        tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
          16 * barη * M.effectiveHorizon ^ 2} := by
    ext data
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h q
    · have heq := tdSquareLateWindowRandomProxy_eq_sourceRateExtend
        M π η T t ht V₀ barη q data
      rw [← heq]
      exact h q
    · have heq := tdSquareLateWindowRandomProxy_eq_sourceRateExtend
        M π η T t ht V₀ barη q data
      rw [heq]
      exact h q
  have hprob : 1 - δ / (2 * T) ≤ (tdSamplingLaw M π T).real
      {data | ∀ q : State,
        tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
          16 * barη * M.effectiveHorizon ^ 2} := by
    rw [← htransport]
    exact hfixedCoord
  have hC : 0 ≤ 16 * barη * M.effectiveHorizon ^ 2 := by positivity
  have hnormEq : {data | ∀ q : State,
      tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
        16 * barη * M.effectiveHorizon ^ 2} =
      {data | ‖tdSourceFixedTerminalProxyVector M π η T t V₀ barη data‖ ≤
        16 * barη * M.effectiveHorizon ^ 2} := by
    ext data
    constructor
    · intro hq
      apply (pi_norm_le_iff_of_nonneg hC).2
      intro q
      have heq := tdSquareLateWindowRandomProxy_eq_sourceRateExtend
        M π η T t ht V₀ barη q data
      have hnonnegExt := tdSquareLateWindowRandomProxy_nonneg
        M π ηext T t V₀ barη hbar0 hηext q data
      have hnonneg : 0 ≤ tdSquareLateWindowRandomProxy M π η T t V₀ barη q data := by
        rw [← heq]
        exact hnonnegExt
      have hcoord := hq q
      simpa [tdSourceFixedTerminalProxyVector, Real.norm_eq_abs] using
        (abs_le.mpr ⟨(neg_nonpos.mpr hC).trans hnonneg, hcoord⟩)
    · intro hn q
      have hcoord := norm_le_pi_norm
        (tdSourceFixedTerminalProxyVector M π η T t V₀ barη data) q
      have heq := tdSquareLateWindowRandomProxy_eq_sourceRateExtend
        M π η T t ht V₀ barη q data
      have hnonnegExt := tdSquareLateWindowRandomProxy_nonneg
        M π ηext T t V₀ barη hbar0 hηext q data
      have hnonneg : 0 ≤ tdSquareLateWindowRandomProxy M π η T t V₀ barη q data := by
        rw [← heq]
        exact hnonnegExt
      have habs : |tdSquareLateWindowRandomProxy M π η T t V₀ barη q data| ≤
          16 * barη * M.effectiveHorizon ^ 2 := by
        simpa [tdSourceFixedTerminalProxyVector, Real.norm_eq_abs] using
          hcoord.trans hn
      exact (abs_le.mp habs).2
  rw [← hnormEq]
  exact hprob

end StatisticalRL.TemporalDifference
