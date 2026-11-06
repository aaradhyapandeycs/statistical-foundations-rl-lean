import Formalization.Online.SourceOptimism.VisitCountFoundation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Pathwise regrouping of arbitrary pre-visit-count costs. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row] [DecidableEq Row]

/-- Every actual row visit contributes the cost indexed by its zero-based
pre-visit count. No stochastic or stage-clock assumption is needed. -/
theorem qLearning_visitCost_regroup (rowAt : ℕ → Row) (K : ℕ) (β : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, β (onlineVisitCount rowAt k (rowAt k))) =
      ∑ r : Row, ∑ n ∈ Finset.range (onlineVisitCount rowAt K r), β n := by
  classical
  induction K with
  | zero => simp [onlineVisitCount_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ,ih]
    have hstep (r : Row) :
        (∑ n ∈ Finset.range (onlineVisitCount rowAt (K+1) r), β n) =
          (∑ n ∈ Finset.range (onlineVisitCount rowAt K r), β n) +
            if rowAt K = r then β (onlineVisitCount rowAt K r) else 0 := by
      rw [onlineVisitCount_succ]
      by_cases hr : rowAt K = r
      · simp [hr,Finset.sum_range_succ]
      · simp [hr]
    simp_rw [hstep,Finset.sum_add_distrib]
    simp
end StatisticalRL.OnlineRL
