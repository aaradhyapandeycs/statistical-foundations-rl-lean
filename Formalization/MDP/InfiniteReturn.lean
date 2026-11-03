import Formalization.MDP.InfiniteTrajectory
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Discounted reward on actual infinite trajectories

Source: arXiv:2610.41903v1, Chapter 2, `eq:defn-Vpi-inf`. The state at time
zero is the supplied initial state; each path pair records the action and the
next state. We define the source's discounted sum and its integral under the
infinite controlled probability law.
-/

open scoped BigOperators Topology
open MeasureTheory Filter

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance infiniteReturnStateMeasurable : MeasurableSpace State := ⊤
local instance infiniteReturnActionMeasurable : MeasurableSpace Action := ⊤

/-- The actual state at time `t` of the sampled path. -/
def trajectoryState (s : State) (path : ℕ → Action × State) : ℕ → State
  | 0 => s
  | n + 1 => (path n).2

/-- The actual discounted reward at source time `t`. -/
def discountedRewardTerm (M : DiscountedMDP State Action) (s : State)
    (path : ℕ → Action × State) (t : ℕ) : ℝ :=
  M.discount ^ t * M.reward (trajectoryState s path t) (path t).1

/-- The actual infinite discounted reward along a controlled trajectory. -/
noncomputable def infiniteDiscountedReturn (M : DiscountedMDP State Action) (s : State)
    (path : ℕ → Action × State) : ℝ :=
  ∑' t, M.discountedRewardTerm s path t

/-- The source value: expectation of the actual infinite return under the
controlled infinite-trajectory probability law. -/
noncomputable def trajectoryExpectedValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  ∫ path, M.infiniteDiscountedReturn s path ∂M.infiniteTrajectoryLaw π s

theorem discountedRewardTerm_nonneg (M : DiscountedMDP State Action) (s : State)
    (path : ℕ → Action × State) (t : ℕ) : 0 ≤ M.discountedRewardTerm s path t :=
  mul_nonneg (pow_nonneg M.discount_nonneg _) (M.reward_nonneg _ _)

theorem discountedRewardTerm_le (M : DiscountedMDP State Action) (s : State)
    (path : ℕ → Action × State) (t : ℕ) :
    M.discountedRewardTerm s path t ≤ M.discount ^ t := by
  calc
    M.discountedRewardTerm s path t ≤ M.discount ^ t * 1 :=
      mul_le_mul_of_nonneg_left (M.reward_le_one _ _) (pow_nonneg M.discount_nonneg _)
    _ = _ := mul_one _

theorem discountedRewardTerm_summable (M : DiscountedMDP State Action) (s : State)
    (path : ℕ → Action × State) : Summable (M.discountedRewardTerm s path) :=
  Summable.of_nonneg_of_le (M.discountedRewardTerm_nonneg s path)
    (M.discountedRewardTerm_le s path)
    (summable_geometric_of_lt_one M.discount_nonneg M.discount_lt_one)

/-- Every sample-path return has the source's geometric bound. -/
theorem infiniteDiscountedReturn_bounds (M : DiscountedMDP State Action) (s : State)
    (path : ℕ → Action × State) :
    0 ≤ M.infiniteDiscountedReturn s path ∧
      M.infiniteDiscountedReturn s path ≤ 1 / (1 - M.discount) := by
  constructor
  · exact tsum_nonneg (M.discountedRewardTerm_nonneg s path)
  · calc
      M.infiniteDiscountedReturn s path ≤ ∑' t : ℕ, M.discount ^ t :=
        (M.discountedRewardTerm_summable s path).tsum_le_tsum
          (M.discountedRewardTerm_le s path)
          (summable_geometric_of_lt_one M.discount_nonneg M.discount_lt_one)
      _ = 1 / (1 - M.discount) := by
        rw [tsum_geometric_of_lt_one M.discount_nonneg M.discount_lt_one, one_div]

omit [Fintype State] [Fintype Action] in
theorem measurable_trajectoryState (s : State) (t : ℕ) :
    Measurable (fun path : ℕ → Action × State ↦ trajectoryState s path t) := by
  cases t with
  | zero => exact measurable_const
  | succ n => exact (measurable_pi_apply n).snd

theorem measurable_discountedRewardTerm (M : DiscountedMDP State Action) (s : State) (t : ℕ) :
    Measurable (fun path : ℕ → Action × State ↦ M.discountedRewardTerm s path t) := by
  have hr : Measurable (fun p : State × Action ↦ M.reward p.1 p.2) := measurable_of_countable _
  exact measurable_const.mul (hr.comp ((measurable_trajectoryState s t).prodMk (measurable_pi_apply t).fst))

/-- The infinite return is measurable as the pointwise limit of measurable
finite discounted reward sums. -/
theorem measurable_infiniteDiscountedReturn (M : DiscountedMDP State Action) (s : State) :
    Measurable (M.infiniteDiscountedReturn s) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n path ↦ ∑ t ∈ Finset.range n, M.discountedRewardTerm s path t)
  · intro n
    exact Finset.measurable_sum _ (fun t _ ↦ M.measurable_discountedRewardTerm s t)
  · apply tendsto_pi_nhds.mpr
    intro path
    exact (M.discountedRewardTerm_summable s path).hasSum.tendsto_sum_nat

/-- The source return is integrable under the actual controlled infinite law. -/
theorem integrable_infiniteDiscountedReturn (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Integrable (M.infiniteDiscountedReturn s) (M.infiniteTrajectoryLaw π s) := by
  refine ⟨(M.measurable_infiniteDiscountedReturn s).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with path
  rw [Real.norm_eq_abs, abs_of_nonneg (M.infiniteDiscountedReturn_bounds s path).1]
  exact (M.infiniteDiscountedReturn_bounds s path).2

/-- The finite prefix sum on the same actual infinite trajectory. -/
def partialDiscountedReturn (M : DiscountedMDP State Action) (s : State)
    (n : ℕ) (path : ℕ → Action × State) : ℝ :=
  ∑ t ∈ Finset.range n, M.discountedRewardTerm s path t

theorem partialDiscountedReturn_bounds (M : DiscountedMDP State Action)
    (s : State) (n : ℕ) (path : ℕ → Action × State) :
    0 ≤ M.partialDiscountedReturn s n path ∧
      M.partialDiscountedReturn s n path ≤ 1 / (1 - M.discount) := by
  constructor
  · exact Finset.sum_nonneg (fun t _ ↦ M.discountedRewardTerm_nonneg s path t)
  · calc
      M.partialDiscountedReturn s n path ≤ M.infiniteDiscountedReturn s path :=
        (M.discountedRewardTerm_summable s path).sum_le_tsum _
          (fun t _ ↦ M.discountedRewardTerm_nonneg s path t)
      _ ≤ _ := (M.infiniteDiscountedReturn_bounds s path).2

theorem measurable_partialDiscountedReturn (M : DiscountedMDP State Action)
    (s : State) (n : ℕ) : Measurable (M.partialDiscountedReturn s n) :=
  Finset.measurable_sum _ (fun t _ ↦ M.measurable_discountedRewardTerm s t)

/-- Expected finite sums on the actual infinite path converge to the actual
source expectation. This does not assume an identification with separately
constructed finite-path laws. -/
theorem tendsto_integral_partialDiscountedReturn (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Tendsto (fun n ↦ ∫ path, M.partialDiscountedReturn s n path ∂M.infiniteTrajectoryLaw π s)
      atTop (𝓝 (M.trajectoryExpectedValue π s)) := by
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

/-- The expected infinite return obeys the source's geometric bound. -/
theorem trajectoryExpectedValue_bounds (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ M.trajectoryExpectedValue π s ∧
      M.trajectoryExpectedValue π s ≤ 1 / (1 - M.discount) := by
  constructor
  · exact integral_nonneg (fun path ↦ (M.infiniteDiscountedReturn_bounds s path).1)
  · calc
      M.trajectoryExpectedValue π s ≤
          ∫ _ : ℕ → Action × State, (1 / (1 - M.discount)) ∂M.infiniteTrajectoryLaw π s :=
        integral_mono (M.integrable_infiniteDiscountedReturn π s) (integrable_const _)
          (fun path ↦ (M.infiniteDiscountedReturn_bounds s path).2)
      _ = _ := by simp

end StatisticalRL.DiscountedMDP
