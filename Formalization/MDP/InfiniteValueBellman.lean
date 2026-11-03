import Formalization.MDP.InfiniteReturn
import Formalization.MDP.InfinitePrefix
import Formalization.MDP.PolicyValueQ
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# First-step identities for the infinite trajectory return

Source: arXiv:2610.41903v1, Chapter 2, `eq:defn-Vpi-inf` and
`eq:bellman_consistency-V`. No Bellman consistency equation is assumed.
-/

open scoped BigOperators Topology
open MeasureTheory Filter

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance infiniteBellmanStateMeasurable : MeasurableSpace State := ⊤
local instance infiniteBellmanActionMeasurable : MeasurableSpace Action := ⊤

/-- The actual tail of an infinite sequence of action/next-state pairs. -/
def trajectoryTail (path : ℕ → Action × State) : ℕ → Action × State :=
  fun n ↦ path (n + 1)

/-- The full discounted return is its first reward plus the discounted return
of its actual shifted tail from the sampled next state. -/
theorem infiniteDiscountedReturn_first_step (M : DiscountedMDP State Action)
    (s : State) (path : ℕ → Action × State) :
    M.infiniteDiscountedReturn s path =
      M.reward s (path 0).1 + M.discount *
        M.infiniteDiscountedReturn (path 0).2 (trajectoryTail path) := by
  unfold infiniteDiscountedReturn
  rw [(M.discountedRewardTerm_summable s path).tsum_eq_zero_add]
  simp only [discountedRewardTerm, trajectoryState, pow_zero, one_mul, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  cases n with
  | zero => simp [trajectoryTail, pow_succ]
  | succ n =>
    simp only [trajectoryTail, pow_succ]
    ring

/-- Expected first reward under the actual infinite law is the policy average
of the initial state's reward. -/
theorem infiniteTrajectory_initial_reward (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    ∫ path, M.reward s (path 0).1 ∂M.infiniteTrajectoryLaw π s =
      (π s).expectation (M.reward s) := by
  have hm : Measurable (fun p : Action × State ↦ M.reward s p.1) := measurable_of_countable _
  have hmap : (∫ path : ℕ → Action × State, M.reward s (path 0).1
      ∂M.infiniteTrajectoryLaw π s) =
      ∫ p : Action × State, M.reward s p.1
        ∂((M.infiniteTrajectoryLaw π s).map (fun path ↦ path 0)) := by
    symm
    exact integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable
  rw [hmap, M.infiniteTrajectoryLaw_first]
  unfold stepMeasure
  rw [PMF.integral_eq_sum, Fintype.sum_prod_type]
  simp only [FiniteDistribution.toPMF_apply, DecisionStage.stepDistribution, stationaryStage,
    ENNReal.toReal_ofReal (mul_nonneg ((π s).prob_nonneg _) ((M.transition s _).prob_nonneg _)),
    smul_eq_mul]
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul, ← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]

/-- The continuation return is measurable as a function of the sampled path,
including its sampled next state. -/
theorem measurable_shiftedReturn (M : DiscountedMDP State Action) :
    Measurable (fun path : ℕ → Action × State ↦
      M.infiniteDiscountedReturn (path 0).2 (trajectoryTail path)) := by
  have hreturn : Measurable (fun p : State × (ℕ → Action × State) ↦
      M.infiniteDiscountedReturn p.1 p.2) :=
    measurable_from_prod_countable_right (fun s ↦ M.measurable_infiniteDiscountedReturn s)
  have htail : Measurable (trajectoryTail : (ℕ → Action × State) → ℕ → Action × State) := by
    apply measurable_pi_lambda
    intro n
    exact measurable_pi_apply (n + 1)
  exact hreturn.comp ((measurable_pi_apply 0).snd.prodMk htail)

/-- The actual shifted continuation is integrable under the original law. -/
theorem integrable_shiftedReturn (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    Integrable (fun path ↦ M.infiniteDiscountedReturn (path 0).2 (trajectoryTail path))
      (M.infiniteTrajectoryLaw π s) := by
  refine ⟨M.measurable_shiftedReturn.aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards with path
  rw [Real.norm_eq_abs, abs_of_nonneg (M.infiniteDiscountedReturn_bounds _ _).1]
  exact (M.infiniteDiscountedReturn_bounds _ _).2

/-- A general first-step identity for the actual infinite expectation. The
continuation is still integrated against the original path law. -/
theorem trajectoryExpectedValue_first_step (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.trajectoryExpectedValue π s = (π s).expectation (M.reward s) + M.discount *
      ∫ path, M.infiniteDiscountedReturn (path 0).2 (trajectoryTail path)
        ∂M.infiniteTrajectoryLaw π s := by
  have hr : Measurable (fun path : ℕ → Action × State ↦ M.reward s (path 0).1) :=
    (measurable_of_countable (M.reward s)).comp (measurable_pi_apply 0).fst
  have hi : Integrable (fun path : ℕ → Action × State ↦ M.reward s (path 0).1)
      (M.infiniteTrajectoryLaw π s) := by
    refine ⟨hr.aestronglyMeasurable, ?_⟩
    apply HasFiniteIntegral.of_bounded
    filter_upwards with path
    rw [Real.norm_eq_abs, abs_of_nonneg (M.reward_nonneg _ _)]
    exact M.reward_le_one _ _
  unfold trajectoryExpectedValue
  calc
    (∫ path, M.infiniteDiscountedReturn s path ∂M.infiniteTrajectoryLaw π s) =
        ∫ path, M.reward s (path 0).1 + M.discount *
          M.infiniteDiscountedReturn (path 0).2 (trajectoryTail path)
            ∂M.infiniteTrajectoryLaw π s := by
      apply integral_congr_ae
      filter_upwards with path
      exact M.infiniteDiscountedReturn_first_step s path
    _ = _ := by
      rw [integral_add hi ((M.integrable_shiftedReturn π s).const_mul _),
        integral_const_mul, M.infiniteTrajectory_initial_reward]

/-- At zero discount, the actual infinite return is the first reward. -/
theorem infiniteDiscountedReturn_of_discount_zero (M : DiscountedMDP State Action)
    (h : M.discount = 0) (s : State) (path : ℕ → Action × State) :
    M.infiniteDiscountedReturn s path = M.reward s (path 0).1 := by
  rw [M.infiniteDiscountedReturn_first_step, h]
  simp

/-- At zero discount, the actual infinite-trajectory value satisfies the
policy Bellman equation. -/
theorem trajectoryExpectedValue_bellman_of_discount_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (h : M.discount = 0) :
    M.valueBellman π (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π := by
  funext s
  change (π s).expectation (M.reward s) + M.discount *
    (M.policyTransition π s).expectation (M.trajectoryExpectedValue π) = _
  rw [h, zero_mul, add_zero]
  unfold trajectoryExpectedValue
  calc
    (π s).expectation (M.reward s) =
        ∫ path, M.reward s (path 0).1 ∂M.infiniteTrajectoryLaw π s :=
      (M.infiniteTrajectory_initial_reward π s).symm
    _ = ∫ path, M.infiniteDiscountedReturn s path ∂M.infiniteTrajectoryLaw π s := by
      apply integral_congr_ae
      filter_upwards with path
      exact (M.infiniteDiscountedReturn_of_discount_zero h s path).symm

/-- The zero-discount infinite expectation equals the unique state Bellman
fixed point. -/
theorem trajectoryExpectedValue_eq_valueFixedPoint_of_discount_zero
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (h : M.discount = 0) : M.trajectoryExpectedValue π = M.valueFixedPoint π :=
  (M.valueFixedPoint_characterization π _).mp
    (M.trajectoryExpectedValue_bellman_of_discount_zero π h)

end StatisticalRL.DiscountedMDP
