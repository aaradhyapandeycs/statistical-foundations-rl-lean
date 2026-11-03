import Formalization.Generative.GenerativeLowerBoundQMixtureTesting

/-! Baseline-versus-mixture risk selection for one common Q estimator. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- A single estimator cannot have risk below 1/4 simultaneously under a
baseline and all mixture alternatives when their baseline separation and
actual-law overlap satisfy the stated inputs. No pairwise alternative
separation is required. -/
theorem finite_mixture_baseline_risk_selection {ι Ω E : Type*}
    [Fintype ι] [Nonempty ι] [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [NormedAddCommGroup E]
    (μ₀ : Measure Ω) (μ : ι → Measure Ω) (mix : Measure Ω)
    [IsProbabilityMeasure μ₀] [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure mix]
    (hmix : ∀ s : Set Ω, mix.real s = (∑ i, (μ i).real s) / Fintype.card ι)
    (hoverlap : (1 : ℝ) / 2 ≤ finiteOverlap μ₀ mix)
    (estimate : Ω → E) (v₀ : E) (v : ι → E) (ε : ℝ)
    (hsep : ∀ i, 2 * ε < ‖v i - v₀‖) :
    (1 : ℝ) / 4 ≤ μ₀.real {x | ε < ‖estimate x - v₀‖} ∨
      ∃ i, (1 : ℝ) / 4 ≤ (μ i).real {x | ε < ‖estimate x - v i‖} := by
  classical
  let test : Ω → Bool := fun x ↦ decide (ε < ‖estimate x - v₀‖)
  have ht := finiteOverlap_le_test_error_sum μ₀ mix test
  have hb : μ₀.real {x | test x = true} = μ₀.real {x | ε < ‖estimate x - v₀‖} := by
    congr 1
    ext x
    simp [test]
  have ha (i : ι) : (μ i).real {x | test x = false} ≤
      (μ i).real {x | ε < ‖estimate x - v i‖} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    have hclose : ‖estimate x - v₀‖ ≤ ε := le_of_not_gt (of_decide_eq_false hx)
    exact (baselineDistanceTest_error_subsets estimate v₀ (v i) ε (hsep i)).2 x hclose
  have hsum : mix.real {x | test x = false} ≤
      (∑ i, (μ i).real {x | ε < ‖estimate x - v i‖}) / Fintype.card ι := by
    rw [hmix]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum (fun i _ ↦ ha i)
  by_cases hbase : (1 : ℝ) / 4 ≤ μ₀.real {x | ε < ‖estimate x - v₀‖}
  · exact Or.inl hbase
  · right
    have havg : (1 : ℝ) / 4 ≤
        (∑ i, (μ i).real {x | ε < ‖estimate x - v i‖}) / Fintype.card ι := by
      rw [hb] at ht
      linarith
    by_contra hnone
    push_neg at hnone
    have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hs : (∑ i, (μ i).real {x | ε < ‖estimate x - v i‖}) <
        ∑ _i : ι, (1 : ℝ) / 4 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ hnone i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hh := (le_div_iff₀ hk).1 havg
    linarith

end StatisticalRL.GenerativeLowerBound
