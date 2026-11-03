import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.OptimalTrajectoryValue

/-!
# Discounted occupancy of the constructed optimal policy

Source: arXiv:2610.41903v1, `eq:defn-dpi-occupancy-discounted-dist-opt`
and `eq:infinite-d-star-def`. The same initial distribution and the same
constructed deterministic greedy policy occur on both sides.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance optimalOccupancyStateMeasurable : MeasurableSpace State := ⊤
local instance optimalOccupancyActionMeasurable : MeasurableSpace Action := ⊤
noncomputable local instance optimalOccupancyStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance optimalOccupancyActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The joint discounted occupancy of the constructed optimal greedy policy
is its state occupancy times the indicator of the greedy action. -/
theorem optimalGreedy_discountedJointOccupancy_indicator
    (M : DiscountedMDP State Action) (ρ : FiniteDistribution State)
    (s : State) (a : Action) :
    M.discountedJointOccupancy M.optimalGreedyPolicy ρ s a =
      M.discountedStateOccupancy M.optimalGreedyPolicy ρ s *
        (if a = M.optimalGreedyAction s then 1 else 0) := by
  exact M.discountedJointOccupancy_deterministic M.optimalGreedyAction ρ s a

/-- The optimal joint occupancy is both the source's actual infinite-path
event sum and the same-policy state occupancy times its action indicator. -/
theorem optimalGreedy_discountedJointOccupancy_source_and_indicator
    (M : DiscountedMDP State Action) (ρ : FiniteDistribution State)
    (s : State) (a : Action) :
    (M.discountedJointOccupancy M.optimalGreedyPolicy ρ s a = (1 - M.discount) *
      ∑' t : ℕ, M.discount ^ t * ρ.expectation (fun x ↦
        (M.infiniteTrajectoryLaw M.optimalGreedyPolicy x).real
          {path | trajectoryState x path t = s ∧ (path t).1 = a})) ∧
    (M.discountedJointOccupancy M.optimalGreedyPolicy ρ s a =
      M.discountedStateOccupancy M.optimalGreedyPolicy ρ s *
        (if a = M.optimalGreedyAction s then 1 else 0)) := by
  exact ⟨M.discountedJointOccupancy_eq_source M.optimalGreedyPolicy ρ s a,
    M.optimalGreedy_discountedJointOccupancy_indicator ρ s a⟩

/-- The very same policy in the indicator identity is simultaneously optimal
for actual trajectory state and forced-action values among stationary
randomized policies. -/
theorem optimalGreedy_trajectory_optimal_and_occupancy
    (M : DiscountedMDP State Action) (ρ : FiniteDistribution State)
    (s : State) (a : Action) :
    (∀ π : StationaryPolicy State Action,
      M.trajectoryExpectedValue π s ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s ∧
      M.trajectoryExpectedQ π s a ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a) ∧
    (M.discountedJointOccupancy M.optimalGreedyPolicy ρ s a =
      M.discountedStateOccupancy M.optimalGreedyPolicy ρ s *
        (if a = M.optimalGreedyAction s then 1 else 0)) := by
  refine ⟨?_, M.optimalGreedy_discountedJointOccupancy_indicator ρ s a⟩
  intro π
  exact ⟨M.trajectoryValue_le_optimalGreedy π s, M.trajectoryQ_le_optimalGreedy π s a⟩

end StatisticalRL.DiscountedMDP
