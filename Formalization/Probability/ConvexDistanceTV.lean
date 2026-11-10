import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Convex.Basic

/-!
# The convex distance is at most the TV distance

Source: `chapters/inference.tex:124–129` (`eqn:convex-distance`: `d_cvx(P,Q) = sup_{A ∈ 𝒞_d}
|P(A) − Q(A)|` over all convex `A ⊆ ℝ^d`; claim `d_cvx(P,Q) ≤ TV(P,Q)` at :129) and
`chapters/intro.tex:223–227` (`eq:TV`: `TV(P,Q) = sup_{A ∈ 𝓕} |P(A) − Q(A)|` over the
σ-algebra).

Reading. Convex sets need not be Borel (an open disc together with an arbitrary subset of its
boundary circle), so `P(A)` for a convex `A` is read as the outer measure `P.real A`
(`Measure` application), as in `Thm7_11_printed_allConvex`. The inequality holds for *every*
set: `exists_measurable_measureReal_eq` gives a measurable `M ⊇ A` with `P(M) = P(A)` and
`Q(M) = Q(A)` simultaneously (the intersection of the two measurable hulls).
-/

open MeasureTheory

namespace StatisticalRL.Ch7Rest.TDInference

variable {α : Type*} [MeasurableSpace α]

/-- A common measurable hull: for any set `C` there is a measurable `M ⊇ C` carrying the outer
measures of `C` under both `P` and `Q`. -/
theorem exists_measurable_measureReal_eq (P Q : Measure α) (C : Set α) :
    ∃ M, MeasurableSet M ∧ C ⊆ M ∧ P M = P C ∧ Q M = Q C := by
  refine ⟨toMeasurable P C ∩ toMeasurable Q C,
    (measurableSet_toMeasurable P C).inter (measurableSet_toMeasurable Q C),
    Set.subset_inter (subset_toMeasurable P C) (subset_toMeasurable Q C), ?_, ?_⟩
  · apply le_antisymm
    · calc P (toMeasurable P C ∩ toMeasurable Q C) ≤ P (toMeasurable P C) :=
            measure_mono Set.inter_subset_left
        _ = P C := measure_toMeasurable C
    · exact measure_mono (Set.subset_inter (subset_toMeasurable P C) (subset_toMeasurable Q C))
  · apply le_antisymm
    · calc Q (toMeasurable P C ∩ toMeasurable Q C) ≤ Q (toMeasurable Q C) :=
            measure_mono Set.inter_subset_right
        _ = Q C := measure_toMeasurable C
    · exact measure_mono (Set.subset_inter (subset_toMeasurable P C) (subset_toMeasurable Q C))

theorem abs_measureReal_sub_le_one (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (C : Set α) : |P.real C - Q.real C| ≤ 1 := by
  have h1 : P.real C ≤ 1 := measureReal_le_one
  have h2 : Q.real C ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ P.real C := measureReal_nonneg
  have h4 : 0 ≤ Q.real C := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

theorem bddAbove_tv (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    BddAbove {x : ℝ | ∃ A, MeasurableSet A ∧ x = |P.real A - Q.real A|} :=
  ⟨1, by rintro _ ⟨A, _, rfl⟩; exact abs_measureReal_sub_le_one P Q A⟩

/-- Every set (measurable or not, read through outer measures) has
`|P(C) − Q(C)| ≤ TV(P, Q)`. -/
theorem abs_measureReal_sub_le_tv (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (C : Set α) :
    |P.real C - Q.real C| ≤
      sSup {x : ℝ | ∃ A, MeasurableSet A ∧ x = |P.real A - Q.real A|} := by
  obtain ⟨M, hM, -, hP, hQ⟩ := exists_measurable_measureReal_eq P Q C
  have : |P.real C - Q.real C| = |P.real M - Q.real M| := by
    simp only [Measure.real, hP, hQ]
  rw [this]
  exact le_csSup (bddAbove_tv P Q) ⟨M, hM, rfl⟩

/-- `d_cvx(P, Q) ≤ TV(P, Q)` (`inference.tex:129`) for laws on `ℝ^ι`, with the supremum over all
convex sets (outer measures on non-measurable ones) and TV the supremum over measurable sets. -/
theorem convexDistance_le_tv {ι : Type*} [Fintype ι] (P Q : Measure (ι → ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    sSup {x : ℝ | ∃ C : Set (ι → ℝ), Convex ℝ C ∧ x = |P.real C - Q.real C|} ≤
      sSup {x : ℝ | ∃ A, MeasurableSet A ∧ x = |P.real A - Q.real A|} := by
  refine csSup_le ⟨|P.real ∅ - Q.real ∅|, ∅, convex_empty, rfl⟩ ?_
  rintro _ ⟨C, -, rfl⟩
  exact abs_measureReal_sub_le_tv P Q C

end StatisticalRL.Ch7Rest.TDInference
