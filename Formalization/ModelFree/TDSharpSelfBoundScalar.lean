import Formalization.ModelFree.TDSharpFreedmanCaps

/-! Nonnegativity of the actual late-window proxy and a deterministic scalar absorption lemma. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSharpSelfBoundStateMeasurable : MeasurableSpace State := ⊤

/-- The actual source proxy is nonnegative: its late-window terms use the
nonnegative rate envelope, discount square, chronological tail rows and true
policy-row variances. The index `n` is retained as the source late window. -/
theorem tdSquareLateWindowRandomProxy_nonneg
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (barη : ℝ)
    (hbar0 : 0 ≤ barη)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i ∧ η i ≤ 1)
    (q : State) (data : TDSamples State T) :
    0 ≤ tdSquareLateWindowRandomProxy M π η T t V₀ barη q data := by
  unfold tdSquareLateWindowRandomProxy
  apply Finset.sum_nonneg
  intro n hn
  by_cases hlate : t / 2 ≤ n
  · simp only [if_pos hlate]
    have hnlt : n < t := Finset.mem_range.mp hn
    have hk : 1 ≤ n + 1 := by omega
    have hkt : n + 1 ≤ t := by omega
    have hηt : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1 :=
      fun i hi1 hit ↦ hη i hi1
    have hrows := tdSquareLateTerminalRow_mass M π η t (n + 1) hk hkt q hηt
    have hinner : 0 ≤ ∑ r, tdSquareLateTerminalRow M π η t (n + 1) q r *
        (M.policyTransition π r).variance
          (tdValueBefore M π η T n V₀ data) := by
      apply Finset.sum_nonneg
      intro r hr
      exact mul_nonneg (hrows.1 r)
        ((M.policyTransition π r).variance_nonneg _)
    have hcoeff : 0 ≤ barη * η (n + 1) * M.discount ^ 2 :=
      mul_nonneg (mul_nonneg hbar0 (hη (n + 1) hk).1)
        (sq_nonneg M.discount)
    exact mul_nonneg hcoeff hinner
  · simp [hlate]

/-- Deterministic absorption for the exact scalar inequality produced by
combining the source energy event with the Freedman radius. Here `a` is the
source late-rate envelope and `L` is the exact Freedman logarithm. The
hypothesis is the intermediate self-bound, not the desired conclusion. -/
theorem tdSquareProxy_scalar_absorption
    (a H L W : ℝ)
    (ha0 : 0 ≤ a) (haHalf : a ≤ 1 / 2)
    (hH0 : 0 ≤ H) (hL0 : 0 ≤ L) (hW0 : 0 ≤ W)
    (hsmall : a * L ≤ 1 / 64)
    (hself : W ≤ a / (1 - a) *
      (3 * H ^ 2 +
        Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
        (8 / 3) * a * H ^ 2 * L)) :
    W ≤ 16 * a * H ^ 2 := by
  have hden : 0 < 1 - a := by linarith
  have hfrac : a / (1 - a) ≤ 2 * a := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr (by linarith : 0 ≤ 1 - 2 * a))]
  have hproxyShift : 0 ≤ W + a * H ^ 2 :=
    add_nonneg hW0 (mul_nonneg ha0 (sq_nonneg H))
  have hrad : 0 ≤ 32 * H ^ 2 * (W + a * H ^ 2) * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg H))
      hproxyShift) hL0
  have hradSmall : 0 ≤ 2 * a * H ^ 2 * (W + a * H ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) (sq_nonneg H))
      hproxyShift
  have hbase : 0 ≤ 3 * H ^ 2 +
      Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
      (8 / 3) * a * H ^ 2 * L := by
    positivity
  have hself' : W ≤ 2 * a *
      (3 * H ^ 2 +
        Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
        (8 / 3) * a * H ^ 2 * L) := by
    calc
      _ ≤ a / (1 - a) *
          (3 * H ^ 2 +
            Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
            (8 / 3) * a * H ^ 2 * L) := hself
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac hbase
  have hselfExpand : W ≤ 6 * a * H ^ 2 +
      2 * a * Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
      (16 / 3) * a ^ 2 * H ^ 2 * L := by
    calc
      _ ≤ 2 * a *
          (3 * H ^ 2 +
            Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
            (8 / 3) * a * H ^ 2 * L) := hself'
      _ = _ := by ring
  have hsmallScaled : 128 * a ^ 2 * L ≤ 2 * a := by
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg (show (0 : ℝ) ≤ 128 by norm_num) ha0)
    nlinarith [hmul]
  have hsmallTimesProxy :
      128 * a ^ 2 * L * (H ^ 2 * (W + a * H ^ 2)) ≤
        2 * a * (H ^ 2 * (W + a * H ^ 2)) :=
    mul_le_mul_of_nonneg_right hsmallScaled
      (mul_nonneg (sq_nonneg H) hproxyShift)
  have hsqrtCompareSq :
      (2 * a * Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L)) ^ 2 ≤
        (Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad, Real.sq_sqrt hradSmall]
    nlinarith [hsmallTimesProxy]
  have hmiddle :
      2 * a * Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) ≤
        Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2)) :=
    (sq_le_sq₀
      (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ha0)
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp hsqrtCompareSq
  have hasquaredRate : a ^ 2 * L ≤ a / 64 := by
    calc
      _ = a * (a * L) := by ring
      _ ≤ a * (1 / 64) := mul_le_mul_of_nonneg_left hsmall ha0
      _ = a / 64 := by ring
  have hlinear : (16 / 3) * a ^ 2 * H ^ 2 * L ≤
      (1 / 12) * a * H ^ 2 := by
    calc
      _ = (16 / 3) * (a ^ 2 * L) * H ^ 2 := by ring
      _ ≤ (16 / 3) * (a / 64) * H ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hasquaredRate (by norm_num))
          (sq_nonneg H)
      _ = (1 / 12) * a * H ^ 2 := by ring
  have hselfReduced : W ≤ (13 / 2) * a * H ^ 2 +
      Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2)) := by
    calc
      _ ≤ 6 * a * H ^ 2 +
          2 * a * Real.sqrt (32 * H ^ 2 * (W + a * H ^ 2) * L) +
          (16 / 3) * a ^ 2 * H ^ 2 * L := hselfExpand
      _ ≤ 6 * a * H ^ 2 +
          Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2)) +
          (1 / 12) * a * H ^ 2 := by
        nlinarith [hmiddle, hlinear]
      _ ≤ (13 / 2) * a * H ^ 2 +
          Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2)) := by
        nlinarith [mul_nonneg ha0 (sq_nonneg H)]
  have htarget : 0 ≤ W / 2 + (3 / 2) * a * H ^ 2 :=
    add_nonneg (div_nonneg hW0 (by norm_num))
      (mul_nonneg
        (mul_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num) ha0)
        (sq_nonneg H))
  have hcompareSq :
      (Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2))) ^ 2 ≤
        (W / 2 + (3 / 2) * a * H ^ 2) ^ 2 := by
    rw [Real.sq_sqrt hradSmall]
    nlinarith [sq_nonneg (W - a * H ^ 2)]
  have hroot : Real.sqrt (2 * a * H ^ 2 * (W + a * H ^ 2)) ≤
      W / 2 + (3 / 2) * a * H ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) htarget).mp hcompareSq
  nlinarith [hselfReduced, hroot]

end StatisticalRL.TemporalDifference
