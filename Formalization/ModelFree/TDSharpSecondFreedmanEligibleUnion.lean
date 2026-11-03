import Formalization.ModelFree.TDSharpSecondFreedman
import Formalization.ModelFree.TDSourceRateProxyTransport

/-!

This module retains the source range `T/(c₂ log T) ≤ t ≤ T` and the finite state/terminal union, with explicit per-terminal rate envelope premises.
-/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpSecondFreedmanEligibleUnionStateMeasurable : MeasurableSpace State := ⊤

/-- Simultaneous actual proxy self-bound over every state and every terminal
satisfying the source range `T/(c₂ log T) ≤ t≤T`. Each state/terminal pair
gets confidence `ε=δ/(2ST)`, and the bad-event union costs at most `δ/2`.
The source late-rate envelope and exact small-step premise remain explicit. -/
theorem tdSquareLateWindowProxy_le_sharp_sourceEligibleTerminals
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (hT : 2 ≤ T) (c₂ : ℝ) (hc₂ : 0 < c₂)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hbar0 : 0 ≤ barη) (hbarHalf : barη ≤ 1 / 2)
    (hbar : ∀ t, t ≤ T → 0 < c₂ * Real.log (T : ℝ) →
      tdSourceEligibleTerminal T c₂ t →
      ∀ k, t / 2 + 1 ≤ k → k ≤ t → η k ≤ barη)
    (K : ℕ) (hK : 0 < K)
    (hKcut : M.effectiveHorizon ≤ (2 : ℝ) ^ K)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : barη * Real.log
      (2 * K / (δ / (2 * (Fintype.card State : ℝ) * T))) ≤ 1 / 64) :
    1 - δ / 2 ≤ (tdSamplingLaw M π T).real {data |
      ∀ q : State, ∀ j : Fin T,
        tdSourceEligibleTerminal T c₂ (j.val + 1) →
        tdSquareLateWindowRandomProxy M π η T (j.val + 1) V₀ barη q data ≤
          16 * barη * M.effectiveHorizon ^ 2} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let μ : Measure (TDSamples State T) := tdSamplingLaw M π T
  let S : ℝ := Fintype.card State
  let ε : ℝ := δ / (2 * S * T)
  have hS : 1 ≤ S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : 0 ≤ (T : ℝ) := by linarith
  have hST : 2 ≤ S * T := by
    calc
      (2 : ℝ) ≤ (T : ℝ) := hTr
      _ = 1 * (T : ℝ) := by ring
      _ ≤ S * (T : ℝ) := mul_le_mul_of_nonneg_right hS hT0
  have hden : 0 < 2 * S * T := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden]
    nlinarith [hδ1, hST]
  have hTreal : 1 < (T : ℝ) := by exact_mod_cast (by omega : 1 < T)
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos hTreal
  have hrateDen : 0 < c₂ * Real.log (T : ℝ) := mul_pos hc₂ hlogT
  have hsmallε : barη * Real.log (2 * K / ε) ≤ 1 / 64 := by
    simpa [ε, S, mul_assoc] using hsmall
  let good (q : State) (t : ℕ) : Set (TDSamples State T) :=
    {data | tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
      16 * barη * M.effectiveHorizon ^ 2}
  let bad (p : State × Fin T) : Set (TDSamples State T) :=
    if tdSourceEligibleTerminal T c₂ (p.2.val + 1) then
      (good p.1 (p.2.val + 1))ᶜ else ∅
  have hbad (p : State × Fin T) : μ.real (bad p) ≤ ε := by
    by_cases hp : tdSourceEligibleTerminal T c₂ (p.2.val + 1)
    · have hu : p.2.val + 1 ≤ T := by omega
      have hgood := tdSquareLateWindowProxy_le_sharp_probability M π η T
        (p.2.val + 1) hu V₀ h₀ hη barη hbar0 hbarHalf
        (hbar (p.2.val + 1) hu hrateDen hp) K hK hKcut ε hε hε1
        (by simpa [ε, S, mul_assoc] using hsmall) p.1
      have hc := measureReal_compl (μ := μ)
        ((Set.to_countable (good p.1 (p.2.val + 1))).measurableSet)
      rw [probReal_univ] at hc
      simp only [bad, hp, if_pos]
      change 1 - ε ≤ μ.real (good p.1 (p.2.val + 1)) at hgood
      linarith
    · simp [bad, hp, hε.le]
  let badUnion : Set (TDSamples State T) := ⋃ p : State × Fin T, bad p
  have hbadUnion : μ.real badUnion ≤ δ / 2 := by
    calc
      _ ≤ ∑ p : State × Fin T, μ.real (bad p) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : State × Fin T, ε :=
        Finset.sum_le_sum fun p _ ↦ hbad p
      _ = δ / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
        dsimp [ε, S]
        field_simp [ne_of_gt hden]
  let target : Set (TDSamples State T) :=
    {data | ∀ q : State, ∀ j : Fin T,
      tdSourceEligibleTerminal T c₂ (j.val + 1) →
        data ∈ good q (j.val + 1)}
  have hsub : badUnionᶜ ⊆ target := by
    intro data hnot q j hj
    by_contra hbad'
    have hmember : data ∈ bad (q, j) := by
      simp [bad, hj, hbad']
    exact hnot (Set.mem_iUnion.mpr ⟨(q, j), hmember⟩)
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ)
    ((Set.to_countable badUnion).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ / 2 ≤ μ.real target
  linarith

end StatisticalRL.TemporalDifference
