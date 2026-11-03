import Formalization.Generative.GenerativeLowerBoundWeightedLog
import Formalization.Generative.GenerativeLowerBoundAffinityOverlap
import Formalization.Generative.GenerativeLowerBoundProductKL
import Formalization.Generative.GenerativeLowerBoundOverlapTesting
import Formalization.Generative.GenerativeLowerBoundTestingReduction
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Finite full-support KL to overlap via Hellinger affinity. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StatisticalRL.GenerativeLowerBound

/-- The source exponential KL-overlap bridge for strictly positive finite
probability vectors. -/
theorem finite_exp_neg_kl_le_two_overlap {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v : ι → ℝ) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hsumu : ∑ i, u i = 1) (hsumv : ∑ i, v i = 1) :
    Real.exp (-finiteKLExpression u v) ≤ 2 * ∑ i, min (u i) (v i) := by
  let A := finiteAffinity u v
  have hA : 0 < A := Finset.sum_pos
    (fun i _ ↦ mul_pos (Real.sqrt_pos.2 (hu i)) (Real.sqrt_pos.2 (hv i))) Finset.univ_nonempty
  have hlog := finite_log_affinity_lower u v hu hv hsumu
  change -finiteKLExpression u v / 2 ≤ Real.log A at hlog
  have he : Real.exp (-finiteKLExpression u v / 2) ≤ A := by
    have := Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log hA] using this
  have he2 := mul_self_le_mul_self (Real.exp_pos _).le he
  have hexp : Real.exp (-finiteKLExpression u v) =
      Real.exp (-finiteKLExpression u v / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hCS := finite_affinity_sq_le_two_overlap u v (fun i ↦ (hu i).le)
    (fun i ↦ (hv i).le) hsumu hsumv
  change A ^ 2 ≤ _ at hCS
  nlinarith

/-- Real KL of two full-support finite probability measures is the oriented
finite sum, with no infinity hidden by conversion. -/
theorem finite_klDiv_eq_expression {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} ≠ 0) :
    (InformationTheory.klDiv μ ν).toReal =
      finiteKLExpression (fun x ↦ μ.real {x}) (fun x ↦ ν.real {x}) := by
  have hac := finite_fullSupport_ac μ ν hν
  have heq : μ Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac heq,
    integral_fintype _ Integrable.of_finite]
  unfold finiteKLExpression
  apply Finset.sum_congr rfl
  intro x _
  rw [MeasureTheory.llr, finite_rnDeriv_apply μ ν hν, ENNReal.toReal_div]
  rfl

/-- Actual finite-law overlap controls the exponential of negative KL. -/
theorem finite_exp_neg_klDiv_le_two_overlap {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, μ {x} ≠ 0) (hν : ∀ x, ν {x} ≠ 0) :
    Real.exp (-(InformationTheory.klDiv μ ν).toReal) ≤ 2 * finiteOverlap μ ν := by
  let u : Ω → ℝ := fun x ↦ μ.real {x}
  let v : Ω → ℝ := fun x ↦ ν.real {x}
  have hu (x : Ω) : 0 < u x := ENNReal.toReal_pos (hμ x) (measure_ne_top μ _)
  have hv (x : Ω) : 0 < v x := ENNReal.toReal_pos (hν x) (measure_ne_top ν _)
  have hu1 : ∑ x, u x = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hv1 : ∑ x, v x = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  rw [finite_klDiv_eq_expression μ ν hν]
  exact finite_exp_neg_kl_le_two_overlap u v hu hv hu1 hv1

/-- The source exponential branch bounds every binary test on two actual
finite full-support laws, with KL oriented from μ to ν. -/
theorem finite_test_error_ge_exp_kl {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, μ {x} ≠ 0) (hν : ∀ x, ν {x} ≠ 0) (test : Ω → Bool) :
    Real.exp (-(InformationTheory.klDiv μ ν).toReal) / 4 ≤
      max (ν.real {x | test x = true}) (μ.real {x | test x = false}) := by
  have ho := finite_exp_neg_klDiv_le_two_overlap μ ν hμ hν
  have ht := finiteOverlap_half_le_max_test_error ν μ test
  have heq : finiteOverlap μ ν = finiteOverlap ν μ := by
    unfold finiteOverlap
    simp only [min_comm]
  rw [heq] at ho
  linarith

/-- The exponential source branch is strictly above 0.1 at β≤0.9. -/
theorem sourceExpBranch_strict (β : ℝ) (hβ : β ≤ 9 / 10) :
    (1 : ℝ) / 10 < Real.exp (-β) / 4 := by
  have heq : Real.exp (-(9 : ℝ) / 10) = Real.exp (-1) * Real.exp (1 / 10) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  have h₁ := Real.exp_neg_one_gt_d9
  have h₂ := Real.add_one_le_exp ((1 : ℝ) / 10)
  have hl : (2 : ℝ) / 5 < Real.exp (-(9 : ℝ) / 10) := by
    rw [heq]
    have hm := mul_nonneg (sub_nonneg.mpr h₂) (Real.exp_pos (-1)).le
    nlinarith
  have hm : Real.exp (-(9 : ℝ) / 10) ≤ Real.exp (-β) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- With finite KL at most 0.9, every binary test has strictly more than
0.1 maximum error under the two actual full-support laws. -/
theorem finite_test_error_gt_one_tenth {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, μ {x} ≠ 0) (hν : ∀ x, ν {x} ≠ 0)
    (hKL : (InformationTheory.klDiv μ ν).toReal ≤ 9 / 10) (test : Ω → Bool) :
    (1 : ℝ) / 10 < max (ν.real {x | test x = true}) (μ.real {x | test x = false}) :=
  (sourceExpBranch_strict _ hKL).trans_le (finite_test_error_ge_exp_kl μ ν hμ hν test)

/-- A concrete quadratic budget implies strict two-point testing difficulty
for the genuine N-fold Bernoulli sampling laws. -/
theorem bernoulliProduct_test_error_gt_one_tenth (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (hbudget : N * (((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ≤ 9 / 10)
    (test : (Fin N → Bool) → Bool) :
    (1 : ℝ) / 10 < max ((bernoulliProductLaw N p hp1.le).real {x | test x = true})
      ((bernoulliProductLaw N q hq1.le).real {x | test x = false}) := by
  have hKL := (bernoulliProduct_klDiv_le_quadratic N q p hp hp1 hq hq1).trans hbudget
  exact finite_test_error_gt_one_tenth (bernoulliProductLaw N q hq1.le)
    (bernoulliProductLaw N p hp1.le) (bernoulliProductLaw_atom_ne_zero N q hq hq1)
    (bernoulliProductLaw_atom_ne_zero N p hp hp1) hKL test

/-- For separated scalar targets, no estimator can make both strict-error
probabilities at most 0.1 under the two actual Bernoulli product laws. -/
theorem bernoulliProduct_estimation_error_gt_one_tenth (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (hbudget : N * (((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ≤ 9 / 10)
    (estimate : (Fin N → Bool) → ℝ) (v₀ v₁ ε : ℝ) (hsep : 2 * ε < v₁ - v₀) :
    (1 : ℝ) / 10 < (bernoulliProductLaw N p hp1.le).real {x | ε < |estimate x - v₀|} ∨
    (1 : ℝ) / 10 < (bernoulliProductLaw N q hq1.le).real {x | ε < |estimate x - v₁|} := by
  apply strict_test_lower_bound_implies_estimation_lower_bound _ _ estimate v₀ v₁ ε (1 / 10) hsep
  intro test
  exact bernoulliProduct_test_error_gt_one_tenth N q p hp hp1 hq hq1 hbudget test

end StatisticalRL.GenerativeLowerBound
