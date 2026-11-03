import Formalization.ModelFree.TDSharpSecondFreedmanEligibleUnion
import Formalization.ModelFree.TDSourceRateProxyTransport

/-!

The source proxy lemma needs a fixed terminal and simultaneous all-state norm event with failure at most δ/(2T). This wrapper spends δ/(2ST) per coordinate.
-/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSourceFixedTerminalProxyStateMeasurable : MeasurableSpace State := ⊤

/-- At one source-eligible terminal, all coordinates of the actual proxy are
bounded simultaneously. The failure budget is exactly δ/(2T), obtained by
spending δ/(2ST) on each state. -/
theorem tdSquareLateWindowProxy_fixedTerminal_allStates
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (hT : 2 ≤ T) (ht : t ≤ T)
    (c₂ : ℝ) (_hc₂ : 0 < c₂) (_helig : tdSourceEligibleTerminal T c₂ t)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hbar0 : 0 ≤ barη) (hbarHalf : barη ≤ 1 / 2)
    (hbar : ∀ k, t / 2 + 1 ≤ k → k ≤ t → η k ≤ barη)
    (K : ℕ) (hK : 0 < K)
    (hKcut : M.effectiveHorizon ≤ (2 : ℝ) ^ K)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : barη * Real.log
      (2 * K / (δ / (2 * (Fintype.card State : ℝ) * T))) ≤ 1 / 64) :
    1 - δ / (2 * T) ≤ (tdSamplingLaw M π T).real {data |
      ∀ q : State,
        tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
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
  have hsmallε : barη * Real.log (2 * K / ε) ≤ 1 / 64 := by
    simpa [ε, S, mul_assoc] using hsmall
  let good (q : State) : Set (TDSamples State T) :=
    {data | tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
      16 * barη * M.effectiveHorizon ^ 2}
  let bad (q : State) : Set (TDSamples State T) := (good q)ᶜ
  have hbad (q : State) : μ.real (bad q) ≤ ε := by
    have hgood := tdSquareLateWindowProxy_le_sharp_probability
      M π η T t ht V₀ h₀ hη barη hbar0 hbarHalf hbar K hK hKcut ε hε hε1
      hsmallε q
    have hc := measureReal_compl (μ := μ)
      ((Set.to_countable (good q)).measurableSet)
    rw [probReal_univ] at hc
    simp only [bad]
    change 1 - ε ≤ μ.real (good q) at hgood
    linarith
  let badUnion : Set (TDSamples State T) := ⋃ q : State, bad q
  have hbadUnion : μ.real badUnion ≤ δ / (2 * T) := by
    calc
      _ ≤ ∑ q : State, μ.real (bad q) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _q : State, ε := Finset.sum_le_sum fun q _ ↦ hbad q
      _ = δ / (2 * T) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [ε, S]
        field_simp
  let target : Set (TDSamples State T) :=
    {data | ∀ q : State, data ∈ good q}
  have hsub : badUnionᶜ ⊆ target := by
    intro data hnot q
    by_contra hbad'
    exact hnot (Set.mem_iUnion.mpr ⟨q, hbad'⟩)
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ)
    ((Set.to_countable badUnion).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ / (2 * T) ≤ μ.real target
  linarith

end StatisticalRL.TemporalDifference
