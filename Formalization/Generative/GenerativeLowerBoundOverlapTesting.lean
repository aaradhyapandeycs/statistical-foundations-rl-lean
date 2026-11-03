import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Testing errors lower-bounded by the overlap of actual finite laws. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Overlap mass of two actual finite probability laws. -/
noncomputable def finiteOverlap {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (μ₀ μ₁ : Measure Ω) : ℝ :=
  ∑ x : Ω, min (μ₀.real {x}) (μ₁.real {x})

/-- Every binary test makes errors on at least the overlap mass, split across
the two data-generating laws. -/
theorem finiteOverlap_le_test_error_sum {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ₀ μ₁ : Measure Ω)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (test : Ω → Bool) :
    finiteOverlap μ₀ μ₁ ≤ μ₀.real {x | test x = true} + μ₁.real {x | test x = false} := by
  classical
  let s₀ := Finset.univ.filter (fun x ↦ test x = true)
  let s₁ := Finset.univ.filter (fun x ↦ test x = false)
  have hs₀ : (s₀ : Set Ω) = {x | test x = true} := by ext x; simp [s₀]
  have hs₁ : (s₁ : Set Ω) = {x | test x = false} := by ext x; simp [s₁]
  rw [← hs₀, ← hs₁, ← sum_measureReal_singleton s₀, ← sum_measureReal_singleton s₁]
  unfold finiteOverlap
  simp only [s₀, s₁, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : test x = true
  · simpa [hx] using (min_le_left (μ₀.real {x}) (μ₁.real {x}))
  · have hx' : test x = false := by cases h : test x <;> simp_all
    simpa [hx'] using (min_le_right (μ₀.real {x}) (μ₁.real {x}))

/-- At least one of the two testing errors is at least half the overlap. -/
theorem finiteOverlap_half_le_max_test_error {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ₀ μ₁ : Measure Ω)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (test : Ω → Bool) :
    finiteOverlap μ₀ μ₁ / 2 ≤
      max (μ₀.real {x | test x = true}) (μ₁.real {x | test x = false}) := by
  have h := finiteOverlap_le_test_error_sum μ₀ μ₁ test
  have h₀ := le_max_left (μ₀.real {x | test x = true}) (μ₁.real {x | test x = false})
  have h₁ := le_max_right (μ₀.real {x | test x = true}) (μ₁.real {x | test x = false})
  linarith

/-- The source's square-root testing branch is strictly above 0.1 at and
below β=0.9; no strict strengthening of the β premise is needed. -/
theorem sourcePinskerBranch_strict (β : ℝ) (hβmax : β ≤ 9 / 10) :
    (1 : ℝ) / 10 < (1 - Real.sqrt (β / 2)) / 2 := by
  have hs : Real.sqrt (β / 2) ≤ Real.sqrt ((9 : ℝ) / 20) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hroot : Real.sqrt ((9 : ℝ) / 20) < 4 / 5 := by
    have hr : 0 ≤ Real.sqrt ((9 : ℝ) / 20) := Real.sqrt_nonneg _
    have hr2 : (Real.sqrt ((9 : ℝ) / 20)) ^ 2 = 9 / 20 := Real.sq_sqrt (by norm_num)
    nlinarith
  linarith

end StatisticalRL.GenerativeLowerBound
