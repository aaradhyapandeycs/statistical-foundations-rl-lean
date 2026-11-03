import Formalization.ModelFree.TDSharpSelfBoundScalar
import Formalization.ModelFree.TDSharpEnergyProxy

/-!

This module contains the actual fixed-terminal second-Freedman event, with random variance retained in the radius. It reuses production energy and self-bound declarations.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpSecondFreedmanStateMeasurable : MeasurableSpace State := ⊤

/-- Actual second-Freedman event and sharp proxy self-bound for one fixed
terminal and coordinate. Source rate, cutoff, and smallness assumptions stay
explicit. The theorem uses the true synchronous sample law and strict past
filtration through the imported actual increment APIs. -/
theorem tdSquareLateWindowProxy_le_sharp_probability
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (barη : ℝ) (hbar0 : 0 ≤ barη) (hbarHalf : barη ≤ 1 / 2)
    (hbar : ∀ k, t / 2 + 1 ≤ k → k ≤ t → η k ≤ barη)
    (K : ℕ) (hK : 0 < K)
    (hKcut : M.effectiveHorizon ≤ (2 : ℝ) ^ K)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1)
    (hsmall : barη * Real.log (2 * K / δ₀) ≤ 1 / 64)
    (q : State) :
    1 - δ₀ ≤ (tdSamplingLaw M π T).real {data |
      tdSquareLateWindowRandomProxy M π η T t V₀ barη q data ≤
        16 * barη * M.effectiveHorizon ^ 2} := by
  let μ : Measure (TDSamples State T) := tdSamplingLaw M π T
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (TDSamples State T)) :=
    tdSampleFiltration T
  let X : ℕ → TDSamples State T → ℝ :=
    tdSquareLateWindowIncrement M π η T t V₀ q
  let W : TDSamples State T → ℝ :=
    tdSquareLateWindowRandomProxy M π η T t V₀ barη q
  let L : ℝ := Real.log (2 * K / δ₀)
  have hlogarg : 1 < (2 : ℝ) * K / δ₀ := by
    rw [lt_div_iff₀ hδ₀]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK))
    nlinarith
  have hL0 : 0 ≤ L := (Real.log_pos hlogarg).le
  have hH0 : 0 ≤ M.effectiveHorizon := M.effectiveHorizon_nonneg
  have hB : 0 ≤ 2 * barη * M.effectiveHorizon ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hbar0) (sq_nonneg _)
  have hσ : 0 ≤ 4 * barη * M.effectiveHorizon ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) hbar0)
      (pow_nonneg M.effectiveHorizon_nonneg 5)
  have hX (n : ℕ) : StronglyMeasurable[ℱ (n + 1)] (X n) := by
    change StronglyMeasurable[tdSampleFiltration T (n + 1)]
      (tdSquareLateWindowIncrement M π η T t V₀ q n)
    by_cases hn : t / 2 ≤ n ∧ n < t
    · simp [tdSquareLateWindowIncrement, hn]
      exact tdSquareTerminalIncrement_strong_nextPast M π η T t ht V₀ q n
    · simp [tdSquareLateWindowIncrement, hn]
      exact stronglyMeasurable_const
  have hinc (n : ℕ) : ∀ᵐ data ∂μ, |X n data| ≤ 2 * barη * M.effectiveHorizon ^ 2 := by
    simpa [X] using tdSquareLateWindowIncrement_abs_le M π η T t ht V₀ h₀
      (fun i hi1 hiT ↦ hη i hi1) barη hbar0 hbar q n
  have hcenter (n : ℕ) :
      μ[X n | ℱ n] =ᵐ[μ] fun _ ↦ 0 := by
    simpa [μ, ℱ, X] using
      tdSquareLateWindowIncrement_condExp_zero M π η T t ht V₀ q n
  have hvarianceProxy :=
    tdSquareLateWindowPredictableVariance_le_randomProxy M π η T t ht V₀ h₀
      hη barη hbar q
  have hcoarse (data : TDSamples State T) :
      W data ≤ barη * M.effectiveHorizon ^ 3 := by
    simpa [W] using tdSquareLateWindowRandomProxy_le_coarse M π η T t ht V₀
      h₀ hη barη hbar0 q data
  have hproxyNonneg (data : TDSamples State T) : 0 ≤ W data := by
    simpa [W] using tdSquareLateWindowRandomProxy_nonneg M π η T t V₀ barη
      hbar0 hη q data
  have hcap : ∀ᵐ data ∂μ,
      predictableSecondMomentSum μ ℱ X t data ≤ 4 * barη * M.effectiveHorizon ^ 5 := by
    filter_upwards [hvarianceProxy] with data hv
    have hv' :
        predictableSecondMomentSum μ ℱ X t data ≤
          4 * M.effectiveHorizon ^ 2 * W data := by
      simpa [μ, ℱ, X, W, tdSquareLateWindowPredictableVariance] using hv
    calc
      _ ≤ 4 * M.effectiveHorizon ^ 2 * W data := hv'
      _ ≤ 4 * M.effectiveHorizon ^ 2 * (barη * M.effectiveHorizon ^ 3) :=
        mul_le_mul_of_nonneg_left (hcoarse data)
          (mul_nonneg (by norm_num) (sq_nonneg M.effectiveHorizon))
      _ = 4 * barη * M.effectiveHorizon ^ 5 := by ring
  have hfree := freedman_source_bound μ ℱ X
    (2 * barη * M.effectiveHorizon ^ 2) (4 * barη * M.effectiveHorizon ^ 5)
    hB hσ hX hinc hcenter t K hK hcap δ₀ hδ₀ hδ₀1
  have henergy := tdSquareLateWindowRandomProxy_le_energy M π η T t ht V₀
    h₀ hη barη hbar0 hbarHalf hbar q
  have hpow : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num) K
  have hcut :
      (4 * barη * M.effectiveHorizon ^ 5) / (2 : ℝ) ^ K ≤
        4 * barη * M.effectiveHorizon ^ 4 := by
    apply (div_le_iff₀ hpow).2
    have hmul := mul_le_mul_of_nonneg_left hKcut
      (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hbar0)
        (pow_nonneg M.effectiveHorizon_nonneg 4))
    nlinarith [hmul]
  have hgoodSubset :
      {data | |incrementSum X t data| ≤
        Real.sqrt (8 * max
          (predictableSecondMomentSum μ ℱ X t data)
          ((4 * barη * M.effectiveHorizon ^ 5) / (2 : ℝ) ^ K) * L) +
          (4 / 3) * (2 * barη * M.effectiveHorizon ^ 2) * L} ≤ᵐ[μ]
      {data | W data ≤ 16 * barη * M.effectiveHorizon ^ 2} := by
    filter_upwards [henergy, hvarianceProxy] with data henergyData hvarianceData
    intro hgood
    have hV : predictableSecondMomentSum μ ℱ X t data ≤
        4 * M.effectiveHorizon ^ 2 * W data := by
      simpa [μ, ℱ, X, W, tdSquareLateWindowPredictableVariance] using hvarianceData
    have hHcoef : 0 ≤ 4 * M.effectiveHorizon ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg M.effectiveHorizon)
    have hmax : max
        (predictableSecondMomentSum μ ℱ X t data)
        ((4 * barη * M.effectiveHorizon ^ 5) / (2 : ℝ) ^ K) ≤
          4 * M.effectiveHorizon ^ 2 *
            (W data + barη * M.effectiveHorizon ^ 2) := by
      apply max_le
      · calc
          _ ≤ 4 * M.effectiveHorizon ^ 2 * W data := hV
          _ ≤ 4 * M.effectiveHorizon ^ 2 *
              (W data + barη * M.effectiveHorizon ^ 2) := by
            nlinarith [mul_nonneg hHcoef
              (mul_nonneg hbar0 (sq_nonneg M.effectiveHorizon))]
      · calc
          _ ≤ 4 * barη * M.effectiveHorizon ^ 4 := hcut
          _ = 4 * M.effectiveHorizon ^ 2 *
              (barη * M.effectiveHorizon ^ 2) := by ring
          _ ≤ 4 * M.effectiveHorizon ^ 2 *
              (W data + barη * M.effectiveHorizon ^ 2) := by
            nlinarith [mul_nonneg hHcoef (hproxyNonneg data)]
    have hrad :
        8 * max
          (predictableSecondMomentSum μ ℱ X t data)
          ((4 * barη * M.effectiveHorizon ^ 5) / (2 : ℝ) ^ K) * L ≤
          32 * M.effectiveHorizon ^ 2 *
            (W data + barη * M.effectiveHorizon ^ 2) * L := by
      calc
        _ ≤ 8 * (4 * M.effectiveHorizon ^ 2 *
            (W data + barη * M.effectiveHorizon ^ 2)) * L :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmax (by norm_num)) hL0
        _ = _ := by ring
    have hroot := Real.sqrt_le_sqrt hrad
    have hsumEq : incrementSum X t data =
        tdSquareLateWindowSum M π η T t V₀ q data := by rfl
    have hfreeData :
        |tdSquareLateWindowSum M π η T t V₀ q data| ≤
          Real.sqrt (8 * max
            (predictableSecondMomentSum μ ℱ X t data)
            ((4 * barη * M.effectiveHorizon ^ 5) / (2 : ℝ) ^ K) * L) +
            (4 / 3) * (2 * barη * M.effectiveHorizon ^ 2) * L := by
      simpa [hsumEq] using hgood
    have hsumBound :
        tdSquareLateWindowSum M π η T t V₀ q data ≤
          Real.sqrt (32 * M.effectiveHorizon ^ 2 *
            (W data + barη * M.effectiveHorizon ^ 2) * L) +
            (8 / 3) * barη * M.effectiveHorizon ^ 2 * L := by
      calc
        _ ≤ |tdSquareLateWindowSum M π η T t V₀ q data| := le_abs_self _
        _ ≤ Real.sqrt (8 * max
            (predictableSecondMomentSum μ ℱ X t data)
            ((4 * barη * M.effectiveHorizon ^ 5) / (2 : ℝ) ^ K) * L) +
            (4 / 3) * (2 * barη * M.effectiveHorizon ^ 2) * L := hfreeData
        _ ≤ Real.sqrt (32 * M.effectiveHorizon ^ 2 *
            (W data + barη * M.effectiveHorizon ^ 2) * L) +
            (4 / 3) * (2 * barη * M.effectiveHorizon ^ 2) * L :=
          add_le_add hroot le_rfl
        _ = _ := by ring
    have hcoef : 0 ≤ barη / (1 - barη) :=
      div_nonneg hbar0 (le_of_lt (by linarith))
    have hself : W data ≤ barη / (1 - barη) *
        (3 * M.effectiveHorizon ^ 2 +
          Real.sqrt (32 * M.effectiveHorizon ^ 2 *
            (W data + barη * M.effectiveHorizon ^ 2) * L) +
          (8 / 3) * barη * M.effectiveHorizon ^ 2 * L) := by
      calc
        _ ≤ barη / (1 - barη) *
            (3 * M.effectiveHorizon ^ 2 +
              tdSquareLateWindowSum M π η T t V₀ q data) := henergyData
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by linarith [hsumBound]) hcoef
    exact tdSquareProxy_scalar_absorption barη M.effectiveHorizon L (W data)
      hbar0 hbarHalf M.effectiveHorizon_nonneg hL0 (hproxyNonneg data)
      (by simpa [L] using hsmall) hself
  exact hfree.trans
    (ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono_ae hgoodSubset))

end StatisticalRL.TemporalDifference
