import Formalization.ModelFree.TDStepSizeEarly
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Standalone TD step-size boundary example

This finite example witnesses that the separately printed TD step-size
estimate does not follow from its displayed schedule and time-feasibility
conditions alone. It uses the literal finite schedule and the source's initial
weight. The hypotheses do not include the main TD accuracy theorem's sample
budget, so this result does not refute that theorem or its budgeted conclusion.

This example does not formalize the main TD theorem.
-/

open scoped BigOperators
namespace StatisticalRL.TemporalDifference

noncomputable def c5Gamma : ℝ := 999999 / 1000000
noncomputable def c5C : ℝ := 1 / 4
noncomputable def c5Rate : ℝ :=
  1 / (1 + c5C * (1 - c5Gamma) * (100 : ℝ) / Real.log (100 : ℝ) ^ 2)
noncomputable def c5Schedule : ℕ → ℝ := fun _ ↦ c5Rate

theorem c5_log_100_ge_four : 4 < Real.log (100 : ℝ) := by
  have he1 : Real.exp 1 < 3 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    simpa only [mul_one] using (Real.exp_nat_mul (1 : ℝ) 4)
  have he4lt : Real.exp 4 < 100 := by
    rw [he4]
    calc
      Real.exp 1 ^ 4 ≤ (3 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_nonneg 1) he1.le 4
      _ < 100 := by norm_num
  have h := Real.log_lt_log (Real.exp_pos 4) he4lt
  rw [Real.log_exp] at h
  exact h

theorem c5_rate_schedule :
    TDStepSizeSchedule c5Gamma c5C c5C 100 c5Schedule := by
  intro i hi hiT
  have hlog : 0 < Real.log (100 : ℝ) := by
    linarith [c5_log_100_ge_four]
  have hgap : 0 < 1 - c5Gamma := by norm_num [c5Gamma]
  have hC : 0 < c5C := by norm_num [c5C]
  have hi_nonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hdenT : 0 < 1 + c5C * (1 - c5Gamma) * (100 : ℝ) /
      Real.log (100 : ℝ) ^ 2 := by positivity
  have hdeni : 0 < 1 + c5C * (1 - c5Gamma) * (i : ℝ) /
      Real.log (100 : ℝ) ^ 2 := by positivity
  have hden_le :
      1 + c5C * (1 - c5Gamma) * (i : ℝ) / Real.log (100 : ℝ) ^ 2 ≤
      1 + c5C * (1 - c5Gamma) * (100 : ℝ) / Real.log (100 : ℝ) ^ 2 := by
    have hiR : (i : ℝ) ≤ 100 := by exact_mod_cast hiT
    have hcoef : 0 ≤ c5C * (1 - c5Gamma) := by positivity
    have hnum : c5C * (1 - c5Gamma) * (i : ℝ) ≤
        c5C * (1 - c5Gamma) * (100 : ℝ) :=
      mul_le_mul_of_nonneg_left hiR hcoef
    have hfrac : c5C * (1 - c5Gamma) * (i : ℝ) / Real.log (100 : ℝ) ^ 2 ≤
        c5C * (1 - c5Gamma) * (100 : ℝ) / Real.log (100 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    linarith [hfrac]
  constructor
  · dsimp [c5Schedule, c5Rate]
    exact le_rfl
  · dsimp [c5Schedule, c5Rate]
    exact one_div_le_one_div_of_le hdeni hden_le

theorem c5_rate_le_one (i : ℕ) : c5Schedule i ≤ 1 := by
  have hlog : 0 < Real.log (100 : ℝ) := by
    linarith [c5_log_100_ge_four]
  have hC : 0 < c5C := by norm_num [c5C]
  have hgap : 0 < 1 - c5Gamma := by norm_num [c5Gamma]
  have hden : 0 < 1 + c5C * (1 - c5Gamma) * (100 : ℝ) /
      Real.log (100 : ℝ) ^ 2 := by positivity
  have hden_ge : 1 ≤ 1 + c5C * (1 - c5Gamma) * (100 : ℝ) /
      Real.log (100 : ℝ) ^ 2 := by
    have hterm : 0 ≤ c5C * (1 - c5Gamma) * (100 : ℝ) /
        Real.log (100 : ℝ) ^ 2 := by positivity
    linarith
  dsimp [c5Schedule, c5Rate]
  apply (div_le_iff₀ hden).2
  simpa only [one_mul] using hden_ge

theorem c5_bernoulli_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfac : 0 ≤ 1 - x := by linarith
      have hmul := mul_le_mul_of_nonneg_right ih hfac
      rw [pow_succ]
      have hstep : 1 - ((n + 1 : ℕ) : ℝ) * x ≤
          (1 - (n : ℝ) * x) * (1 - x) := by
        rw [Nat.cast_succ]
        nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]
      exact hstep.trans hmul

theorem c5_initial_weight_fails_standalone_bound :
    (1 / 2 : ℝ) ≤ c5Gamma ∧ c5Gamma < 1 ∧
      0 < c5C ∧ c5C ≤ c5C ∧ c5C * c5C ≤ 1 / 8 ∧
      2 ≤ 100 ∧ 100 ≤ 100 ∧
      TDStepSizeSchedule c5Gamma c5C c5C 100 c5Schedule ∧
      (100 : ℝ) / (c5C * Real.log (100 : ℝ)) ≤ 100 ∧
      tdRateWeight c5Gamma c5Schedule 100 0 > 1 / (100 : ℝ) ^ 2 := by
  have hparams :
      (1 / 2 : ℝ) ≤ c5Gamma ∧ c5Gamma < 1 ∧
      0 < c5C ∧ c5C ≤ c5C ∧ c5C * c5C ≤ 1 / 8 := by
    norm_num [c5Gamma, c5C]
  have hlog : 0 < Real.log (100 : ℝ) := by
    linarith [c5_log_100_ge_four]
  have htime : (100 : ℝ) / (c5C * Real.log (100 : ℝ)) ≤ 100 := by
    apply (div_le_iff₀ (mul_pos (by norm_num [c5C]) hlog)).2
    have hh : 1 ≤ c5C * Real.log (100 : ℝ) := by
      norm_num [c5C]
      linarith [c5_log_100_ge_four]
    nlinarith [hh]
  have hC : 0 < c5C := by norm_num [c5C]
  have hgap : 0 < 1 - c5Gamma := by norm_num [c5Gamma]
  have hrate : ∀ i, 1 ≤ i → i ≤ 100 → 0 ≤ c5Schedule i ∧ c5Schedule i ≤ 1 := by
    intro i hi hiT
    refine ⟨?_, c5_rate_le_one i⟩
    have hden : 0 < 1 + c5C * (1 - c5Gamma) * (100 : ℝ) /
        Real.log (100 : ℝ) ^ 2 := by positivity
    exact le_of_lt (one_div_pos.mpr hden)
  have hfactor : ∀ i ∈ Finset.Icc 1 100,
      c5Gamma ≤ tdRateContraction c5Gamma c5Schedule i := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hη := c5_rate_le_one i
    have hgap : 0 ≤ 1 - c5Gamma := by norm_num [c5Gamma]
    unfold tdRateContraction
    nlinarith [mul_le_mul_of_nonneg_right hη hgap]
  have hprod : c5Gamma ^ 100 ≤
      ∏ i ∈ Finset.Icc 1 100, tdRateContraction c5Gamma c5Schedule i := by
    calc
      c5Gamma ^ 100 = ∏ _i ∈ Finset.Icc 1 100, c5Gamma := by
        rw [Finset.prod_const, Nat.card_Icc]
      _ ≤ ∏ i ∈ Finset.Icc 1 100, tdRateContraction c5Gamma c5Schedule i :=
        Finset.prod_le_prod
          (by intro i hi; exact (by norm_num [c5Gamma] : 0 ≤ c5Gamma))
          (by intro i hi; exact hfactor i hi)
  have hbern := c5_bernoulli_lower (1 / 1000000 : ℝ)
    (by norm_num) (by norm_num) 100
  have hbern' : (9999 : ℝ) / 10000 ≤
      (1 - (1 : ℝ) / 1000000) ^ 100 := by
    calc
      (9999 : ℝ) / 10000 = 1 - (100 : ℝ) * (1 / 1000000 : ℝ) := by norm_num
      _ ≤ (1 - (1 / 1000000 : ℝ)) ^ 100 := hbern
  have hpow : (9999 : ℝ) / 10000 ≤ c5Gamma ^ 100 := by
    rw [show c5Gamma = 1 - (1 : ℝ) / 1000000 by norm_num [c5Gamma]]
    exact hbern'
  have hweight : tdRateWeight c5Gamma c5Schedule 100 0 >
      1 / (100 : ℝ) ^ 2 := by
    rw [tdRateWeight_initial]
    have hlarge : (1 : ℝ) / (100 : ℝ) ^ 2 < (9999 : ℝ) / 10000 := by norm_num
    exact hlarge.trans_le (hpow.trans hprod)
  exact ⟨hparams.1, hparams.2.1, hparams.2.2.1, hparams.2.2.2.1,
    hparams.2.2.2.2, by omega, by omega, c5_rate_schedule, htime, hweight⟩

end StatisticalRL.TemporalDifference
