import Formalization.OfflineRL.OccupancyWeightedVariance
import Formalization.MDP.DiscountedOccupancyFlow
import Formalization.Probability.VarianceDefinitions

/-!
# `lem:sum-d-Var-UB` for actual MDP objects

The deterministic variance-propagation bound of `OccupancyWeightedVariance.lean`, applied to the
actual policy transition rows of a finite discounted MDP and the actual discounted state
occupancy `d_ρ^π` (whose flow equation is `discountedStateOccupancy_flow`).
-/

open scoped BigOperators

namespace StatisticalRL.OfflineRL.BonusSummation
open StatisticalRL.DiscountedMDP

/-- For any stationary policy `π`, initial law `ρ`, value-like vector `0 ≤ V ≤ 1/(1-γ)` and
penalty `b ≥ 0` with `0 ≤ V - γ P_π V + 2b`:
`∑_s d_ρ^π(s) Var_{P_π(s)}(V) ≤ 2/(γ²(1-γ)) + 4/(γ²(1-γ)) ⟨d_ρ^π, b⟩`. -/
theorem occupancyWeightedVariance_mdp {State Action : Type*} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (V b : State → ℝ)
    (hγ : 0 < M.discount)
    (hV0 : ∀ s, 0 ≤ V s) (hV1 : ∀ s, V s ≤ 1 / (1 - M.discount))
    (hb : ∀ s, 0 ≤ b s)
    (hres : ∀ s, 0 ≤ V s - M.discount * (M.policyTransition π s).expectation V + 2 * b s) :
    ∑ s, M.discountedStateOccupancy π ρ s * (M.policyTransition π s).variance V ≤
      2 / (M.discount ^ 2 * (1 - M.discount)) +
        (4 / (M.discount ^ 2 * (1 - M.discount))) *
          ∑ s, M.discountedStateOccupancy π ρ s * b s := by
  have h := occupancyWeightedVariance (fun s t ↦ (M.policyTransition π s).prob t)
    (M.discountedStateOccupancy π ρ) ρ.prob V b M.discount hγ M.discount_lt_one
    (fun s t ↦ (M.policyTransition π s).prob_nonneg t)
    (fun s ↦ (M.policyTransition π s).sum_prob)
    (fun s ↦ M.discountedStateOccupancy_nonneg π ρ s) ρ.prob_nonneg ρ.sum_prob
    (fun s ↦ M.discountedStateOccupancy_flow π ρ s) hV0 hV1 hb
    (fun s ↦ by simpa [FiniteDistribution.expectation] using hres s)
  simpa [FiniteDistribution.variance, FiniteDistribution.expectation] using h

end StatisticalRL.OfflineRL.BonusSummation
