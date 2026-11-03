import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Two-point testing reduction for actual finite-sample laws. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.GenerativeLowerBound

/-- The midpoint test chooses the second hypothesis on ties. -/
noncomputable def midpointTest {Ω : Type*} (estimate : Ω → ℝ) (v₀ v₁ : ℝ) (ω : Ω) : Bool :=
  decide ((v₀ + v₁) / 2 ≤ estimate ω)

/-- A 2ε-separated pair makes midpoint misclassification imply strict
estimation error greater than ε, including the tie convention. -/
theorem midpointTest_error_implies_estimation_error {Ω : Type*}
    (estimate : Ω → ℝ) (v₀ v₁ ε : ℝ) (hsep : 2 * ε < v₁ - v₀) (ω : Ω) :
    (midpointTest estimate v₀ v₁ ω = true → ε < |estimate ω - v₀|) ∧
    (midpointTest estimate v₀ v₁ ω = false → ε < |estimate ω - v₁|) := by
  constructor
  · intro h
    have hm : (v₀ + v₁) / 2 ≤ estimate ω := of_decide_eq_true h
    have ha := le_abs_self (estimate ω - v₀)
    linarith
  · intro h
    have hm : estimate ω < (v₀ + v₁) / 2 := lt_of_not_ge (of_decide_eq_false h)
    have ha := neg_le_abs (estimate ω - v₁)
    linarith

/-- Every midpoint testing error is bounded by the corresponding actual
estimation-error probability under either supplied probability measure. -/
theorem midpointTest_error_probability_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (μ₀ μ₁ : Measure Ω) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (estimate : Ω → ℝ) (v₀ v₁ ε : ℝ) (hsep : 2 * ε < v₁ - v₀) :
    μ₀.real {ω | midpointTest estimate v₀ v₁ ω = true} ≤
        μ₀.real {ω | ε < |estimate ω - v₀|} ∧
    μ₁.real {ω | midpointTest estimate v₀ v₁ ω = false} ≤
        μ₁.real {ω | ε < |estimate ω - v₁|} := by
  constructor
  · apply measureReal_mono _ (measure_ne_top μ₀ _)
    intro ω hω
    exact (midpointTest_error_implies_estimation_error estimate v₀ v₁ ε hsep ω).1 hω
  · apply measureReal_mono _ (measure_ne_top μ₁ _)
    intro ω hω
    exact (midpointTest_error_implies_estimation_error estimate v₀ v₁ ε hsep ω).2 hω

/-- A strict lower bound on the error of every binary test transfers to a
strict estimation-risk lower bound for at least one of the two laws. -/
theorem strict_test_lower_bound_implies_estimation_lower_bound
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (μ₀ μ₁ : Measure Ω) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (estimate : Ω → ℝ) (v₀ v₁ ε c : ℝ) (hsep : 2 * ε < v₁ - v₀)
    (htest : ∀ test : Ω → Bool,
      c < max (μ₀.real {ω | test ω = true}) (μ₁.real {ω | test ω = false})) :
    c < μ₀.real {ω | ε < |estimate ω - v₀|} ∨
      c < μ₁.real {ω | ε < |estimate ω - v₁|} := by
  have he := midpointTest_error_probability_le μ₀ μ₁ estimate v₀ v₁ ε hsep
  have hl := htest (midpointTest estimate v₀ v₁)
  rcases lt_max_iff.mp hl with h₀ | h₁
  · exact Or.inl (h₀.trans_le he.1)
  · exact Or.inr (h₁.trans_le he.2)

end StatisticalRL.GenerativeLowerBound
