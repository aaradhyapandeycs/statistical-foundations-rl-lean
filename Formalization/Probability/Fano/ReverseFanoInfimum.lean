import Formalization.Probability.Fano.ReverseTest
import Formalization.Probability.Fano.TestTransports

/-!
# Reverse-Fano bound for the source testing-error infima

Translation of `lem:reverse-Fano-bound` (`chapters/prelim.tex:1209–1229`) for
the actual average/minimax error infima over measurable tests, with the
square-root term rearranged into `ℝ≥0∞` so that an infinite KL sum is meaningful
(the bound is then trivial) rather than collapsed by `toReal`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatisticalRL.PrelimFano

/-- The average error of a measurable test is the source's normalized sum. -/
theorem averageTestError_fin_eq {Ω : Type*} [MeasurableSpace Ω] (M : ℕ)
    (P : Fin (M+1) → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (ψ : MeasurableTest (Ω := Ω) (I := Fin (M+1))) :
    averageTestError P ψ =
      (1 / ((M : ℝ) + 1)) * ∑ j : Fin (M+1), (P j).real {ω | ψ.1 ω ≠ j} := by
  unfold averageTestError testError
  rw [Fintype.card_fin]
  push_cast
  ring

theorem averageErrorInfimum_nonneg {Ω : Type*} [MeasurableSpace Ω] (M : ℕ)
    (P : Fin (M+1) → Measure Ω) [∀ j, IsProbabilityMeasure (P j)] :
    0 ≤ averageErrorInfimum P := by
  apply lower_bound_averageErrorInfimum_of_forall_tests P 0
  intro ψ
  rw [averageTestError_fin_eq M P ψ]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => measureReal_nonneg)

/-- Finite-budget real form (the printed inequality): for any `B ≥ 0` bounding
the KL sum, `1 - 1/(M+1) - √(M B / (2(M+1)²))` is at most the average-error
infimum. -/
theorem reverseFano_averageErrorInfimum_lower_of_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin (M+1) → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (B : ℝ) (hB : 0 ≤ B)
    (hKL : (∑ j : Fin M, InformationTheory.klDiv (P 0) (P j.succ)) ≤ ENNReal.ofReal B) :
    1 - 1 / ((M : ℝ)+1) - Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ)+1)^2)) ≤
      averageErrorInfimum P := by
  apply lower_bound_averageErrorInfimum_of_forall_tests P
  intro ψ
  rw [averageTestError_fin_eq M P ψ]
  exact reverseFano_test_error_lower M P ψ.1 ψ.2 B hB hKL

/-- Reverse-Fano bound for the source error infima (frozen signature). -/
theorem reverseFano_infimum_lower
     {Ω : Type*} [MeasurableSpace Ω]
     (M : ℕ) (P : Fin (M+1) → Measure Ω)
     [∀ j, IsProbabilityMeasure (P j)] :
     averageErrorInfimum P ≤ minimaxErrorInfimum P ∧
       ENNReal.ofReal (1 - 1 / ((M : ℝ)+1)) ≤
         ENNReal.ofReal (averageErrorInfimum P) +
           (ENNReal.ofReal ((M : ℝ) / (2 * ((M : ℝ)+1)^2)) *
             ∑ j : Fin M, InformationTheory.klDiv (P 0) (P j.succ)) ^ (1/2 : ℝ) := by
  refine ⟨averageErrorInfimum_le_minimaxErrorInfimum P, ?_⟩
  set S : ℝ≥0∞ := ∑ j : Fin M, InformationTheory.klDiv (P 0) (P j.succ) with hS
  set c : ℝ := (M : ℝ) / (2 * ((M : ℝ)+1)^2) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  by_cases hStop : S = ∞
  · -- Infinite KL sum: necessarily `M > 0`, so the right summand is `∞`.
    have hMpos : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · exfalso
        subst h
        simp [hS] at hStop
      · exact h
    have hcpos : 0 < c := by
      rw [hc]
      have : (0 : ℝ) < M := by exact_mod_cast hMpos
      positivity
    have hcne : ENNReal.ofReal c ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hcpos
    rw [hStop, ENNReal.mul_top hcne, ENNReal.top_rpow_of_pos (by norm_num)]
    simp
  · -- Finite KL sum: choose `B = S.toReal` after proving finiteness.
    set B : ℝ := S.toReal with hBdef
    have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
    have hSB : S = ENNReal.ofReal B := (ENNReal.ofReal_toReal hStop).symm
    have hreal := reverseFano_averageErrorInfimum_lower_of_budget M P B hB0 (le_of_eq hSB)
    have havg0 := averageErrorInfimum_nonneg M P
    have hsq0 : 0 ≤ Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ)+1)^2)) := Real.sqrt_nonneg _
    have hroot : (ENNReal.ofReal c * S) ^ (1/2 : ℝ) =
        ENNReal.ofReal (Real.sqrt ((M : ℝ) * B / (2 * ((M : ℝ)+1)^2))) := by
      rw [hSB, ← ENNReal.ofReal_mul hc0,
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc0 hB0) (by norm_num),
        Real.sqrt_eq_rpow]
      congr 2
      rw [hc]
      ring
    rw [hroot, ← ENNReal.ofReal_add havg0 hsq0]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end StatisticalRL.PrelimFano
