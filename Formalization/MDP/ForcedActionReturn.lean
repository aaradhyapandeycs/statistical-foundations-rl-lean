import Formalization.MDP.InfiniteReturn
import Formalization.MDP.ForcedActionTrajectory

/-!
# Infinite discounted return with its first action forced

Source: arXiv:2610.41903v1, `defn:Qpi-inf-horizon`. The forced first action
is a genuine intervention, meaningful even when the policy assigns it zero
mass. Its expectation is taken under the actual forced-action trajectory law.
Identification with the Q Bellman fixed point remains a separate obligation.
-/

open MeasureTheory Filter
open scoped Topology

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance forcedReturnStateMeasurable : MeasurableSpace State := ⊤
local instance forcedReturnActionMeasurable : MeasurableSpace Action := ⊤

/-- The actual discounted return is integrable under the forced first-action law. -/
theorem integrable_infiniteDiscountedReturn_forced (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    Integrable (M.infiniteDiscountedReturn s) (M.forcedActionTrajectoryLaw π s a) := by
  refine ⟨(M.measurable_infiniteDiscountedReturn s).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with path
  rw [Real.norm_eq_abs, abs_of_nonneg (M.infiniteDiscountedReturn_bounds s path).1]
  exact (M.infiniteDiscountedReturn_bounds s path).2

/-- Source Q as the expectation of actual infinite reward under the
first-action intervention and the original policy thereafter. -/
noncomputable def trajectoryExpectedQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) : ℝ :=
  ∫ path, M.infiniteDiscountedReturn s path ∂M.forcedActionTrajectoryLaw π s a

/-- Expected actual finite prefixes converge to the forced-action expectation. -/
theorem tendsto_integral_partialDiscountedReturn_forced (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    Tendsto (fun n ↦ ∫ path, M.partialDiscountedReturn s n path ∂M.forcedActionTrajectoryLaw π s a)
      atTop (𝓝 (M.trajectoryExpectedQ π s a)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1 / (1 - M.discount))
  · intro n
    exact (M.measurable_partialDiscountedReturn s n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards with path
    rw [Real.norm_eq_abs, abs_of_nonneg (M.partialDiscountedReturn_bounds s n path).1]
    exact (M.partialDiscountedReturn_bounds s n path).2
  · filter_upwards with path
    exact (M.discountedRewardTerm_summable s path).hasSum.tendsto_sum_nat

/-- The source's geometric bound also holds for every forced initial action. -/
theorem trajectoryExpectedQ_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    0 ≤ M.trajectoryExpectedQ π s a ∧
      M.trajectoryExpectedQ π s a ≤ 1 / (1 - M.discount) := by
  constructor
  · exact integral_nonneg (fun path ↦ (M.infiniteDiscountedReturn_bounds s path).1)
  · calc
      M.trajectoryExpectedQ π s a ≤
          ∫ _ : ℕ → Action × State, (1 / (1 - M.discount)) ∂M.forcedActionTrajectoryLaw π s a :=
        integral_mono (M.integrable_infiniteDiscountedReturn_forced π s a) (integrable_const _)
          (fun path ↦ (M.infiniteDiscountedReturn_bounds s path).2)
      _ = _ := by simp

end StatisticalRL.DiscountedMDP
