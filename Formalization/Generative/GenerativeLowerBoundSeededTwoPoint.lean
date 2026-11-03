import Formalization.Generative.GenerativeLowerBoundRandomSeed
import Formalization.Generative.GenerativeLowerBoundKLAffinity

/-! Strict two-point testing with one independent finite seed. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Testing errors are averaged as a sum before selecting a hard model. -/
theorem finiteSeed_test_error_gt_one_tenth {Ω Ξ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (μ ν : Measure Ω) (σ : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hμ : ∀ x, μ {x} ≠ 0) (hν : ∀ x, ν {x} ≠ 0)
    (hKL : (InformationTheory.klDiv μ ν).toReal ≤ 9 / 10)
    (test : Ω × Ξ → Bool) :
    (1 : ℝ) / 10 < max ((independentSeedLaw ν σ).real {z | test z = true})
      ((independentSeedLaw μ σ).real {z | test z = false}) := by
  classical
  have he := finite_exp_neg_klDiv_le_two_overlap μ ν hμ hν
  have hm : finiteOverlap μ ν = finiteOverlap ν μ := by
    unfold finiteOverlap
    simp only [min_comm]
  rw [hm] at he
  have hex := sourceExpBranch_strict _ hKL
  have hover : (1 : ℝ) / 5 < finiteOverlap ν μ := by linarith
  let w (r : Ξ) : ℝ := σ.real {r}
  have hw (r : Ξ) : 0 ≤ w r := measureReal_nonneg
  have hw1 : ∑ r, w r = 1 := by
    dsimp [w]
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have htest (r : Ξ) := finiteOverlap_le_test_error_sum ν μ (fun x ↦ test (x,r))
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_right (htest r) (hw r))
  rw [← Finset.mul_sum, hw1, mul_one] at hs
  rw [independentSeedLaw_real_event, independentSeedLaw_real_event]
  have heq : (∑ r, (ν.real {x | test (x,r) = true} + μ.real {x | test (x,r) = false}) * w r) =
      (∑ r, ν.real {x | test (x,r) = true} * w r) +
      (∑ r, μ.real {x | test (x,r) = false} * w r) := by
    simp [add_mul, Finset.sum_add_distrib]
  rw [heq] at hs
  change (1 : ℝ) / 10 < max
    (∑ r, ν.real {x | test (x,r) = true} * w r)
    (∑ r, μ.real {x | test (x,r) = false} * w r)
  have h0 := le_max_left (∑ r, ν.real {x | test (x,r) = true} * w r)
    (∑ r, μ.real {x | test (x,r) = false} * w r)
  have h1 := le_max_right (∑ r, ν.real {x | test (x,r) = true} * w r)
    (∑ r, μ.real {x | test (x,r) = false} * w r)
  linarith

end StatisticalRL.GenerativeLowerBound
