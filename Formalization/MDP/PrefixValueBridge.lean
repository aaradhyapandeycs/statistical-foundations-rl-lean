import Formalization.MDP.FinitePrefixBridge
import Formalization.MDP.InfiniteReturn
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Identifying infinite and finite trajectory values via finite prefixes -/

open scoped BigOperators Topology
open MeasureTheory Filter
namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance prefixValueStateMeasurable : MeasurableSpace State := ⊤
local instance prefixValueActionMeasurable : MeasurableSpace Action := ⊤

/-- Split the actual finite reward sum after its first sample. -/
theorem partialDiscountedReturn_first_step (M : DiscountedMDP State Action) (s : State)
    (n : ℕ) (path : ℕ → Action × State) :
    M.partialDiscountedReturn s (n + 1) path = M.reward s (path 0).1 + M.discount *
      M.partialDiscountedReturn (path 0).2 n (fun t ↦ path (t + 1)) := by
  unfold partialDiscountedReturn
  rw [Finset.sum_range_succ']
  simp only [discountedRewardTerm, trajectoryState, pow_zero, one_mul, Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | zero => simp [pow_succ]
  | succ i => simp only [pow_succ]; ring

/-- Every prefix return equals the finite-path return on the exact prefix. -/
theorem partialDiscountedReturn_eq_finitePath (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (stages : List (DecisionStage State Action))
    (hstage : ∀ x ∈ stages, x = M.stationaryStage π) (s : State)
    (path : ℕ → Action × State) :
    M.partialDiscountedReturn s stages.length path =
      DecisionStage.discountedPathReward M.discount stages s (finitePrefix stages path) := by
  induction stages generalizing s path with
  | nil => simp [partialDiscountedReturn, DecisionStage.discountedPathReward]
  | cons stage tail ih =>
    have hs : stage = M.stationaryStage π := hstage stage (by simp)
    subst stage
    have ht : ∀ x ∈ tail, x = M.stationaryStage π := by
      intro x hx
      exact hstage x (by simp [hx])
    have hh := finitePrefix_cons_head (M.stationaryStage π) tail path
    have htpath := finitePrefix_cons_tail (M.stationaryStage π) tail path
    change M.partialDiscountedReturn s (tail.length + 1) path = _
    rw [M.partialDiscountedReturn_first_step, ih ht]
    change M.reward s (path 0).1 + M.discount *
      DecisionStage.discountedPathReward M.discount tail (path 0).2
        (finitePrefix tail (fun n ↦ path (n + 1))) = _
    change _ = M.reward s (finitePrefix (M.stationaryStage π :: tail) path).1 +
      M.discount * DecisionStage.discountedPathReward M.discount tail
        (finitePrefix (M.stationaryStage π :: tail) path).2.1
        (finitePrefix (M.stationaryStage π :: tail) path).2.2
    rw [htpath]
    have ha := congrArg Prod.fst hh
    have hs := congrArg Prod.snd hh
    simp only at ha hs
    rw [ha, hs]

/-- The finite prefix is measurable for each stage list. -/
theorem measurable_finitePrefix (stages : List (DecisionStage State Action)) :
    Measurable (finitePrefix stages : (ℕ → Action × State) → FinitePath State Action stages.length) := by
  cases stages with
  | nil => exact measurable_const
  | cons stage tail =>
    change Measurable ((historyToFinitePath tail) ∘
      (fun path : ℕ → Action × State ↦ Preorder.frestrictLe tail.length path))
    exact (measurable_of_countable _).comp (by fun_prop)

/-- Finite simplex expectation agrees with the integral under its PMF measure. -/
private theorem finiteDistribution_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    ∫ x, f x ∂d.toPMF.toMeasure = d.expectation f := by
  rw [PMF.integral_eq_sum]
  simp only [FiniteDistribution.toPMF_apply, ENNReal.toReal_ofReal (d.prob_nonneg _),
    smul_eq_mul, FiniteDistribution.expectation]

/-- Actual infinite-law prefix expectations agree with the independently
constructed finite-trajectory expectations at every horizon. -/
theorem integral_partialDiscountedReturn_eq_finiteDiscountedValue
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (n : ℕ) :
    (∫ path, M.partialDiscountedReturn s n path ∂M.infiniteTrajectoryLaw π s) =
      M.finiteDiscountedValue π n s := by
  let stages := List.replicate n (M.stationaryStage π)
  have ht : ∀ x ∈ stages, x = M.stationaryStage π := by
    intro x hx
    exact (List.mem_replicate.mp hx).2
  have heq (path : ℕ → Action × State) : M.partialDiscountedReturn s n path =
      DecisionStage.discountedPathReward M.discount stages s (finitePrefix stages path) := by
    simpa only [stages, List.length_replicate] using
      M.partialDiscountedReturn_eq_finitePath π stages ht s path
  calc
    (∫ path, M.partialDiscountedReturn s n path ∂M.infiniteTrajectoryLaw π s) =
        ∫ path, DecisionStage.discountedPathReward M.discount stages s (finitePrefix stages path)
          ∂M.infiniteTrajectoryLaw π s := integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = ∫ path, DecisionStage.discountedPathReward M.discount stages s path
          ∂((M.infiniteTrajectoryLaw π s).map (finitePrefix stages)) := by
      symm
      exact integral_map (measurable_finitePrefix stages).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable
    _ = ∫ path, DecisionStage.discountedPathReward M.discount stages s path
          ∂(DecisionStage.trajectoryLaw stages s).toPMF.toMeasure := by
      rw [M.infiniteTrajectoryLaw_map_finitePrefix π stages ht s]
    _ = M.finiteDiscountedValue π n s := by
      exact finiteDistribution_integral _ _

/-- The source's actual infinite-path expectation equals the uniquely
constructed policy state-value Bellman fixed point, for every discount in the
full source range. -/
theorem trajectoryExpectedValue_eq_valueFixedPoint
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    M.trajectoryExpectedValue π = M.valueFixedPoint π := by
  funext s
  apply tendsto_nhds_unique (M.tendsto_integral_partialDiscountedReturn π s)
  have hlim := (tendsto_pi_nhds.mp (M.tendsto_finiteDiscountedValue π)) s
  simpa only [M.integral_partialDiscountedReturn_eq_finiteDiscountedValue π s] using hlim

end StatisticalRL.DiscountedMDP
