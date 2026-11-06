import Formalization.Probability.Fano.TestRiskDefinitions
import Formalization.Probability.Fano.FinitePartitionKL
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace StatisticalRL.PrelimFano

section Testing

variable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
  [Fintype I] [Nonempty I] [MeasurableSingletonClass I]

private theorem card_positive_real : (0 : ℝ) < Fintype.card I := by
  exact_mod_cast Fintype.card_pos

private theorem testError_nonneg (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)]
    (ψ : MeasurableTest (Ω := Ω) (I := I)) (i : I) : 0 ≤ testError P ψ i :=
  measureReal_nonneg

private theorem averageTestError_nonneg (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (ψ : MeasurableTest (Ω := Ω) (I := I)) :
    0 ≤ averageTestError P ψ := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ ↦ testError_nonneg P ψ i)
  · exact card_positive_real.le

private theorem worstTestError_nonneg (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (ψ : MeasurableTest (Ω := Ω) (I := I)) :
    0 ≤ worstTestError P ψ := by
  rcases ‹Nonempty I› with ⟨i⟩
  exact (testError_nonneg P ψ i).trans
    (Finset.le_sup' _ (Finset.mem_univ i))

private theorem measurableTest_nonempty :
    Nonempty (MeasurableTest (Ω := Ω) (I := I)) := by
  classical
  exact ⟨⟨fun _ ↦ Classical.choice ‹Nonempty I›, measurable_const⟩⟩

private theorem averageRisk_range_nonempty (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] :
    (Set.range (averageTestError P)).Nonempty := by
  rcases measurableTest_nonempty (Ω := Ω) (I := I) with ⟨ψ⟩
  exact ⟨averageTestError P ψ, ⟨ψ, rfl⟩⟩

private theorem worstRisk_range_nonempty (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] :
    (Set.range (worstTestError P)).Nonempty := by
  rcases measurableTest_nonempty (Ω := Ω) (I := I) with ⟨ψ⟩
  exact ⟨worstTestError P ψ, ⟨ψ, rfl⟩⟩

private theorem averageRisk_range_bddBelow (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] : BddBelow (Set.range (averageTestError P)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨ψ, rfl⟩
  exact averageTestError_nonneg P ψ

private theorem worstRisk_range_bddBelow (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] : BddBelow (Set.range (worstTestError P)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨ψ, rfl⟩
  exact worstTestError_nonneg P ψ

/-- For every actual measurable test, its average error is no larger than its
worst-hypothesis error. -/
theorem averageTestError_le_worstTestError (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)]
    (ψ : MeasurableTest (Ω := Ω) (I := I)) :
    averageTestError P ψ ≤ worstTestError P ψ := by
  have hc := card_positive_real (I := I)
  apply (div_le_iff₀ hc).2
  calc
    ∑ i : I, testError P ψ i ≤
        ∑ _i : I, worstTestError P ψ :=
      Finset.sum_le_sum (fun i _ ↦ Finset.le_sup' _ (Finset.mem_univ i))
    _ = worstTestError P ψ * (Fintype.card I : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- The source minimax infimum dominates the source average-error infimum.
This proves the order of infima for the same set of actual measurable tests. -/
theorem averageErrorInfimum_le_minimaxErrorInfimum (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] :
    averageErrorInfimum P ≤ minimaxErrorInfimum P := by
  apply le_csInf (worstRisk_range_nonempty P)
  intro y hy
  rcases hy with ⟨ψ, rfl⟩
  have hInf : averageErrorInfimum P ≤ averageTestError P ψ :=
    csInf_le (averageRisk_range_bddBelow P) ⟨ψ, rfl⟩
  exact hInf.trans (averageTestError_le_worstTestError P ψ)

/-- A pointwise lower bound valid for every measurable test passes to the
source average-error infimum. -/
theorem lower_bound_averageErrorInfimum_of_forall_tests (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (c : ℝ)
    (h : ∀ ψ : MeasurableTest (Ω := Ω) (I := I), c ≤ averageTestError P ψ) :
    c ≤ averageErrorInfimum P := by
  apply le_csInf (averageRisk_range_nonempty P)
  intro y hy
  rcases hy with ⟨ψ, rfl⟩
  exact h ψ

/-- Exact error preservation under pushing a law through its own measurable
test. This is the classification-law bridge for arbitrary measurable source
spaces; only the test codomain is finite. -/
theorem testError_eq_identityError_of_map (P : I → Measure Ω)
    (ψ : MeasurableTest (Ω := Ω) (I := I)) (i : I) :
    (P i).real {x | ψ.1 x ≠ i} =
      ((P i).map ψ.1).real {y : I | y ≠ i} := by
  have hset : {y : I | y ≠ i} = ({i} : Set I)ᶜ := by
    ext y; simp
  rw [hset]
  simp only [MeasureTheory.measureReal_def]
  rw [Measure.map_apply ψ.2 ((measurableSet_singleton i).compl)]
  rfl

/-- ADDED BY CLAUDE (not in Data's frozen input): pushing a probability law
through an actual measurable test is a probability law. The frozen statement of
`averageTestError_eq_pushed_identityError` requires this instance for the pushed
family and does not elaborate without it. `IsProbabilityMeasure` is a `Prop`, so
this instance does not change the meaning of any statement. -/
instance measurableTest_map_isProbabilityMeasure {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ψ : MeasurableTest (Ω := Ω) (I := I)) : IsProbabilityMeasure (μ.map ψ.1) :=
  Measure.isProbabilityMeasure_map ψ.2.aemeasurable

/-- The average error of the original test is exactly the identity-classifier
error in the finite pushed-forward experiment. -/
theorem averageTestError_eq_pushed_identityError (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)]
    (ψ : MeasurableTest (Ω := Ω) (I := I)) :
    averageTestError P ψ =
      averageTestError (fun i ↦ (P i).map ψ.1)
        ⟨id, measurable_id⟩ := by
  unfold averageTestError
  apply congrArg (fun x : ℝ ↦ x / Fintype.card I)
  apply Finset.sum_congr rfl
  intro i _
  exact testError_eq_identityError_of_map P ψ i

/-- Finite-valued KL data processing applies separately to every law in the
actual testing family. Its source-space carrier remains arbitrary. -/
theorem testPushforward_klDiv_le (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] (i j : I)
    (ψ : MeasurableTest (Ω := Ω) (I := I)) :
    InformationTheory.klDiv ((P i).map ψ.1) ((P j).map ψ.1) ≤
      InformationTheory.klDiv (P i) (P j) :=
  finiteValued_klDiv_map_le (P i) (P j) ψ.1 ψ.2

/-- The KL budget for any fixed test's finite-valued output laws is no larger
than the corresponding source-law budget, term by term over an arbitrary
finite collection of alternatives. -/
theorem testPushforward_alternativeKL_sum_le
    {J : Type*} [Fintype J]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (baseline : I) (alternative : J → I)
    (ψ : MeasurableTest (Ω := Ω) (I := I)) :
    (∑ j : J, InformationTheory.klDiv
      ((P (alternative j)).map ψ.1) ((P baseline).map ψ.1)) ≤
      ∑ j : J, InformationTheory.klDiv (P (alternative j)) (P baseline) := by
  apply Finset.sum_le_sum
  intro j _
  exact testPushforward_klDiv_le P (alternative j) baseline ψ


end Testing

end StatisticalRL.PrelimFano
