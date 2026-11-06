import Formalization.Probability.BernoulliPinsker
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.DenselyOrdered



/-! Canonical all-endpoint Bernoulli Pinsker law bridge for Fano testing. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatisticalRL.GenerativeLowerBound

/-- Scalar Pinsker inequality with the first parameter allowed at the endpoints
`0` and `1` (using Lean's `0 * log 0 = 0`), by continuity from the interior. -/
theorem bernoulliKLExpression_quadratic_lower_closed (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have hform : ∀ x : ℝ, x * Real.log (x / q) + (1 - x) * Real.log ((1 - x) / (1 - q)) =
      x * Real.log x - x * Real.log q +
        ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - q)) := by
    intro x
    have e1 : x * Real.log (x / q) = x * Real.log x - x * Real.log q := by
      rcases eq_or_ne x 0 with h | h
      · simp [h]
      · rw [Real.log_div h hq.ne']; ring
    have e2 : (1 - x) * Real.log ((1 - x) / (1 - q)) =
        (1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - q) := by
      rcases eq_or_ne (1 - x) 0 with h | h
      · simp [h]
      · rw [Real.log_div h (sub_pos.2 hq1).ne']; ring
    rw [e1, e2]
  let F : ℝ → ℝ := fun x => x * Real.log x - x * Real.log q +
    ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - q)) - 2 * (x - q) ^ 2
  have hFc : Continuous F := by
    have h1 : Continuous fun x : ℝ => x * Real.log x := Real.continuous_mul_log
    have h2 : Continuous fun x : ℝ => (1 - x) * Real.log (1 - x) :=
      h1.comp (continuous_const.sub continuous_id)
    have h3 : Continuous fun x : ℝ => x * Real.log q := continuous_id.mul continuous_const
    have h4 : Continuous fun x : ℝ => (1 - x) * Real.log (1 - q) :=
      (continuous_const.sub continuous_id).mul continuous_const
    have h5 : Continuous fun x : ℝ => 2 * (x - q) ^ 2 :=
      continuous_const.mul ((continuous_id.sub continuous_const).pow 2)
    exact ((h1.sub h3).add (h2.sub h4)).sub h5
  have hsub : Ioo (0 : ℝ) 1 ⊆ {x | 0 ≤ F x} := by
    intro x hx
    have hx' := bernoulliKLExpression_quadratic_lower x q hx.1 hx.2 hq hq1
    have hfx := hform x
    show 0 ≤ F x
    simp only [F]
    linarith
  have hclosed : IsClosed {x | 0 ≤ F x} := isClosed_le continuous_const hFc
  have hcl : Icc (0 : ℝ) 1 ⊆ {x | 0 ≤ F x} := by
    rw [← closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.2 hsub
  have hFp : 0 ≤ F p := hcl ⟨hp0, hp1⟩
  simp only [F] at hFp
  have hfp := hform p
  linarith

/-- For a full-support PMF on `Bool`, the Radon–Nikodym derivative is the ratio
of atom masses at every atom. -/
theorem bernoulliPinskerLaw_rnDeriv_apply (P Q : PMF Bool) (hQ : ∀ b, Q b ≠ 0)
    (hac : P.toMeasure ≪ Q.toMeasure) (b : Bool) :
    P.toMeasure.rnDeriv Q.toMeasure b = P b / Q b := by
  have h := Measure.setLIntegral_rnDeriv hac ({b} : Set Bool)
  rw [lintegral_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  apply (ENNReal.eq_div_iff (hQ b) (PMF.apply_ne_top Q b)).2
  simpa [mul_comm] using h

/-- All-endpoint Bernoulli-law Pinsker inequality (frozen signature). -/
theorem bernoulli_klDiv_quadratic_lower (p q : ℝ≥0)
     (hp : p ≤ 1) (hq : q ≤ 1) :
     ENNReal.ofReal (2 * ((p : ℝ) - (q : ℝ))^2) ≤
       InformationTheory.klDiv (PMF.bernoulli p hp).toMeasure
         (PMF.bernoulli q hq).toMeasure := by
  by_cases hpq : p = q
  · subst hpq
    simp [InformationTheory.klDiv_self]
  by_cases htop : InformationTheory.klDiv (PMF.bernoulli p hp).toMeasure
      (PMF.bernoulli q hq).toMeasure = ∞
  · rw [htop]
    exact le_top
  have hac := (InformationTheory.klDiv_ne_top_iff.mp htop).1
  -- Absolute continuity forces `0 < q`.
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le (zero_le q) with h | h
    · exfalso
      have hQ : (PMF.bernoulli q hq).toMeasure {true} = 0 := by
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
        simp [← h]
      have hP := hac hQ
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.bernoulli_apply] at hP
      simp only [cond_true, ENNReal.coe_eq_zero] at hP
      exact hpq (hP.trans h)
    · exact h
  -- Absolute continuity forces `q < 1`.
  have hq1 : q < 1 := by
    rcases eq_or_lt_of_le hq with h | h
    · exfalso
      have hQ : (PMF.bernoulli q hq).toMeasure {false} = 0 := by
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
        simp [h]
      have hP := hac hQ
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.bernoulli_apply] at hP
      simp only [cond_false, ENNReal.coe_eq_zero] at hP
      have hp1 : 1 ≤ p := tsub_eq_zero_iff_le.mp hP
      exact hpq ((le_antisymm hp hp1).trans h.symm)
    · exact h
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  set P := PMF.bernoulli p hp with hPdef
  set Q := PMF.bernoulli q hq with hQdef
  have hQ : ∀ b, Q b ≠ 0 := by
    intro b
    cases b
    · rw [hQdef, PMF.bernoulli_apply]
      simp only [cond_false, ne_eq, ENNReal.coe_eq_zero]
      exact (tsub_pos_of_lt hq1).ne'
    · rw [hQdef, PMF.bernoulli_apply]
      simp only [cond_true, ne_eq, ENNReal.coe_eq_zero]
      exact hq0.ne'
  have heq : P.toMeasure Set.univ = Q.toMeasure Set.univ := by
    rw [measure_univ, measure_univ]
  have hval : (InformationTheory.klDiv P.toMeasure Q.toMeasure).toReal =
      (p : ℝ) * Real.log ((p : ℝ) / (q : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))) := by
    rw [InformationTheory.toReal_klDiv_of_measure_eq hac heq, PMF.integral_eq_sum]
    simp only [Fintype.sum_bool, smul_eq_mul, MeasureTheory.llr,
      bernoulliPinskerLaw_rnDeriv_apply P Q hQ hac]
    simp [P, Q, PMF.bernoulli_apply, ENNReal.toReal_div, hp, hq]
  rw [hval]
  exact bernoulliKLExpression_quadratic_lower_closed p q p.2 (by exact_mod_cast hp)
    (by exact_mod_cast hq0) (by exact_mod_cast hq1)

end StatisticalRL.GenerativeLowerBound
