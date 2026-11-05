import Formalization.Analysis.StochasticResolventOrder
import Formalization.MDP.PolicyMatrixDefinitions

open scoped BigOperators Matrix
namespace StatisticalRL

theorem stochasticMatrix_resolvent_properties {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    stochasticResolventProperties P γ := by
  have hsum := stochasticMatrix_discounted_powers_summable P hp hs γ hγ hγ1
  have hu : IsUnit (1 - γ • P) :=
    ⟨⟨1 - γ • P, ∑' n : ℕ, (γ • P)^n,
      hsum.one_sub_mul_tsum_pow, hsum.tsum_pow_mul_one_sub⟩, rfl⟩
  refine ⟨hu, stochasticMatrix_resolvent_series P hp hs γ hγ hγ1, ?_,
    stochasticMatrix_resolvent_rowNorm P hp hs γ hγ hγ1,
    stochasticMatrix_resolvent_nonneg P hp hs γ hγ hγ1⟩
  funext i
  simpa only [Matrix.mulVec, dotProduct, mul_one] using
    stochasticMatrix_resolvent_rowSum P hp hs γ hγ hγ1 i

namespace DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Source Lemma 2.3 for every stationary randomized policy and both matrices. -/
theorem policyMatrices_resolvent_properties
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    letI := Classical.decEq State
    letI := Classical.decEq Action
    stochasticResolventProperties (M.policyStateTransitionMatrix π) M.discount ∧
    stochasticResolventProperties (M.policyStateActionTransitionMatrix π) M.discount := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  constructor
  · apply stochasticMatrix_resolvent_properties _ _ _ _ M.discount_nonneg M.discount_lt_one
    · intro s t
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg ((π s).prob_nonneg a) ((M.transition s a).prob_nonneg t)
    · intro s
      change ∑ t, ∑ a, (π s).prob a * (M.transition s a).prob t = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
      exact (π s).sum_prob
  · apply stochasticMatrix_resolvent_properties _ _ _ _ M.discount_nonneg M.discount_lt_one
    · intro sa tb
      exact mul_nonneg ((M.transition sa.1 sa.2).prob_nonneg tb.1)
        ((π tb.1).prob_nonneg tb.2)
    · intro sa
      change ∑ tb : State × Action,
        (M.transition sa.1 sa.2).prob tb.1 * (π tb.1).prob tb.2 = 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
      exact (M.transition sa.1 sa.2).sum_prob

end DiscountedMDP
end StatisticalRL
