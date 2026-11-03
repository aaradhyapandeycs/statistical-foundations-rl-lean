import Formalization.ModelFree.QLearningRobustComparator
import Formalization.Probability.EmpiricalRow
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Finite row KL ≤ χ², retaining the source zero-support rule. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.QLearning

variable {State : Type*} [Fintype State]
local instance qChiKLStateMeasurable : MeasurableSpace State := ⊤

/-- The discrete atomic KL expression is bounded by the support-aware
χ² expression. At nominal zero atoms, both laws vanish; no division there is
used. -/
theorem qChi_finiteKLExpression_le (p q : FiniteDistribution State)
    (hs : ∀ x, p.prob x = 0 → q.prob x = 0) :
    StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun x ↦ q.prob x) (fun x ↦ p.prob x) ≤ qChiSquared p q := by
  classical
  let S := Finset.univ.filter (fun x ↦ 0 < p.prob x)
  have hpzero_of_not_mem (x : State) (hx : x ∉ S) : p.prob x = 0 := by
    have hn : ¬ 0 < p.prob x := by simpa [S] using hx
    exact le_antisymm (le_of_not_gt hn) (p.prob_nonneg x)
  have hqSupportSum : ∑ x ∈ S, q.prob x = 1 := by
    calc
      ∑ x ∈ S, q.prob x = ∑ x, q.prob x := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hnot
        have hp0 := hpzero_of_not_mem x hnot
        simp [hs x hp0]
      _ = 1 := q.sum_prob
  have hpSupportSum : ∑ x ∈ S, p.prob x = 1 := by
    calc
      ∑ x ∈ S, p.prob x = ∑ x, p.prob x := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hnot
        simp [hpzero_of_not_mem x hnot]
      _ = 1 := p.sum_prob
  have hmass : ∑ x ∈ S, (q.prob x - p.prob x) = 0 := by
    rw [Finset.sum_sub_distrib, hqSupportSum, hpSupportSum]
    ring
  have hrestrict :
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun x ↦ q.prob x) (fun x ↦ p.prob x) =
        ∑ x ∈ S, q.prob x * Real.log (q.prob x / p.prob x) := by
    unfold StatisticalRL.GenerativeLowerBound.finiteKLExpression
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hp0 := hpzero_of_not_mem x hnot
    simp [hs x hp0]
  have hterm (x : State) (hx : x ∈ S) :
      q.prob x * Real.log (q.prob x / p.prob x) ≤
        (q.prob x - p.prob x)^2 / p.prob x + (q.prob x - p.prob x) := by
    have hp : 0 < p.prob x := (Finset.mem_filter.mp hx).2
    by_cases hq : q.prob x = 0
    · rw [hq]
      have hdiv : p.prob x ≠ 0 := ne_of_gt hp
      field_simp [hdiv]
      norm_num
    · have hqpos : 0 < q.prob x := lt_of_le_of_ne (q.prob_nonneg x) (Ne.symm hq)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqpos hp)
      calc
        q.prob x * Real.log (q.prob x / p.prob x) ≤
            q.prob x * (q.prob x / p.prob x - 1) :=
          mul_le_mul_of_nonneg_left hlog (q.prob_nonneg x)
        _ = (q.prob x - p.prob x)^2 / p.prob x + (q.prob x - p.prob x) := by
          field_simp [ne_of_gt hp]
          ring
  calc
    StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun x ↦ q.prob x) (fun x ↦ p.prob x) =
      ∑ x ∈ S, q.prob x * Real.log (q.prob x / p.prob x) := hrestrict
    _ ≤ ∑ x ∈ S,
        ((q.prob x - p.prob x)^2 / p.prob x + (q.prob x - p.prob x)) :=
      Finset.sum_le_sum fun x hx ↦ hterm x hx
    _ = qChiSquared p q := by
      rw [Finset.sum_add_distrib, hmass]
      simp [qChiSquared, S]

private theorem qChi_rowMeasure_real_singleton (d : FiniteDistribution State) (x : State) :
    d.rowMeasure.real {x} = d.prob x := by
  rw [measureReal_def, FiniteDistribution.rowMeasure,
    d.toPMF.toMeasure_apply_singleton x (measurableSet_singleton x)]
  simp [FiniteDistribution.toPMF_apply, ENNReal.toReal_ofReal, d.prob_nonneg x]

/-- The support condition gives actual absolute continuity of the two row
measures, including when either row has zero atoms. -/
theorem qChi_rowMeasure_absolutelyContinuous (p q : FiniteDistribution State)
    (hs : ∀ x, p.prob x = 0 → q.prob x = 0) : q.rowMeasure ≪ p.rowMeasure := by
  classical
  intro A hA
  have hAmeas : MeasurableSet A := by simp
  have hdisj : Disjoint p.toPMF.support A := by
    apply (p.toPMF.toMeasure_apply_eq_zero_iff hAmeas).mp
    simpa [FiniteDistribution.rowMeasure] using hA
  have hsupport : q.toPMF.support ⊆ p.toPMF.support := by
    intro x hx
    have hqne : q.prob x ≠ 0 := by
      intro hq0
      apply (PMF.mem_support_iff q.toPMF x).mp hx
      simp [FiniteDistribution.toPMF_apply, hq0]
    have hpne : p.prob x ≠ 0 := by
      intro hp0
      exact hqne (hs x hp0)
    have hppos : 0 < p.prob x := lt_of_le_of_ne (p.prob_nonneg x) (Ne.symm hpne)
    apply (PMF.mem_support_iff p.toPMF x).mpr
    simpa [FiniteDistribution.toPMF_apply] using hppos
  have hqdisj : Disjoint q.toPMF.support A := by
    apply Set.disjoint_left.mpr
    intro x hxq hxA
    exact (Set.disjoint_left.mp hdisj) (hsupport hxq) hxA
  apply (q.toPMF.toMeasure_apply_eq_zero_iff hAmeas).mpr hqdisj

/-- Actual finite measure KL of supported rows is bounded by their source
χ² sum. This is the row inequality used by the robust stability argument. -/
theorem qChi_rowKL_le (p q : FiniteDistribution State)
    (hs : ∀ x, p.prob x = 0 → q.prob x = 0) :
    (InformationTheory.klDiv q.rowMeasure p.rowMeasure).toReal ≤ qChiSquared p q := by
  have hac := qChi_rowMeasure_absolutelyContinuous p q hs
  rw [StatisticalRL.GenerativeLowerBound.finite_klDiv_eq_expression_of_ac
    q.rowMeasure p.rowMeasure hac]
  simp_rw [qChi_rowMeasure_real_singleton]
  exact qChi_finiteKLExpression_le p q hs

end StatisticalRL.QLearning
