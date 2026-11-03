import Formalization.MDP.FiniteTrajectory
import Formalization.MDP.FixedPoint

/-!
# Discounted finite trajectory returns

The source's infinite discounted value is an expectation on an infinite path.
This module constructs actual discounted rewards on finite sampled paths and
proves their expectation obeys the corresponding one-step equation. The
identification with an infinite-path expectation remains a separate task.
Source: arXiv:2610.41903v1, Chapter 2, `eq:defn-Vpi-inf` and
`eq:bellman_consistency-V-all`.
-/

open Filter
open scoped Topology NNReal

namespace StatisticalRL.DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The discounted sum of actual rewards stored along a finite sampled path. -/
def discountedPathReward (γ : ℝ) : (stages : List (DecisionStage State Action)) →
    State → FinitePath State Action stages.length → ℝ
  | [], _, _ => 0
  | stage :: tail, s, path =>
    stage.reward s path.1 + γ * discountedPathReward γ tail path.2.1 path.2.2

/-- Expected discounted finite return, with the same trajectory law as the
undiscounted source construction. -/
def discountedTrajectoryValue (γ : ℝ) (stages : List (DecisionStage State Action))
    (s : State) : ℝ :=
  (trajectoryLaw stages s).expectation (discountedPathReward γ stages s)

@[simp]
theorem discountedTrajectoryValue_nil (γ : ℝ) (s : State) :
    discountedTrajectoryValue γ ([] : List (DecisionStage State Action)) s = 0 := by
  exact (trajectoryLaw [] s).expectation_const 0

/-- A discounted stage backup on a genuine randomized policy and transition. -/
def discountedValueBackup (γ : ℝ) (stage : DecisionStage State Action)
    (V : State → ℝ) (s : State) : ℝ :=
  (stage.policy s).expectation (fun a ↦
    stage.reward s a + γ * (stage.transition s a).expectation V)

/-- First-step decomposition, obtained from the actual joint trajectory law. -/
theorem discountedTrajectoryValue_cons (γ : ℝ) (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) :
    discountedTrajectoryValue γ (stage :: tail) s =
      discountedValueBackup γ stage (discountedTrajectoryValue γ tail) s := by
  unfold discountedTrajectoryValue
  rw [trajectoryExpectation_cons]
  change (stage.policy s).expectation (fun a ↦
      (stage.transition s a).expectation (fun t ↦
        (trajectoryLaw tail t).expectation (fun path ↦
          stage.reward s a + γ * discountedPathReward γ tail t path))) = _
  simp_rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const,
    FiniteDistribution.expectation_mul]
  unfold discountedValueBackup
  rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_mul]

end StatisticalRL.DecisionStage

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A stationary discounted model and policy interpreted as one actual stage. -/
def stationaryStage (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    DecisionStage State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := M.transition
  reward := M.reward
  reward_nonneg := M.reward_nonneg
  reward_le_one := M.reward_le_one
  policy := π

/-- The path-derived backup equals the source's policy value Bellman operator. -/
theorem stationary_discountedBackup (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) (s : State) :
    DecisionStage.discountedValueBackup M.discount (M.stationaryStage π) V s =
      M.valueBellman π V s := by
  unfold DecisionStage.discountedValueBackup valueBellman policyTransition stationaryStage
  rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_mul,
    FiniteDistribution.expectation_bind]

/-- Expected discounted reward over `n` actual stationary controlled stages. -/
def finiteDiscountedValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) : State → ℝ :=
  DecisionStage.discountedTrajectoryValue M.discount (List.replicate n (M.stationaryStage π))

@[simp]
theorem finiteDiscountedValue_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : M.finiteDiscountedValue π 0 = 0 := by
  funext s
  exact DecisionStage.discountedTrajectoryValue_nil _ _

/-- The finite path law gives the actual value Bellman recurrence. -/
theorem finiteDiscountedValue_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    M.finiteDiscountedValue π (n + 1) = M.valueBellman π (M.finiteDiscountedValue π n) := by
  funext s
  unfold finiteDiscountedValue
  rw [List.replicate_succ, DecisionStage.discountedTrajectoryValue_cons,
    stationary_discountedBackup]

/-- Finite-trajectory expectations are actual zero-start Bellman iterates. -/
theorem finiteDiscountedValue_eq_iterate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    M.finiteDiscountedValue π n = (M.valueBellman π)^[n] 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [finiteDiscountedValue_succ, ih, Function.iterate_succ_apply']

theorem valueBellman_lipschitz (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    LipschitzWith M.discountConstant (M.valueBellman π) := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simpa only [dist_eq_norm, coe_discountConstant] using M.norm_valueBellman_sub_le π V W

theorem valueBellman_contracting (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ContractingWith M.discountConstant (M.valueBellman π) :=
  ⟨M.discount_lt_one, M.valueBellman_lipschitz π⟩

/-- The state-value Bellman equation has a unique solution on the whole
finite state-function carrier. -/
theorem value_fixedPoint_exists_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ∃! V : State → ℝ, M.valueBellman π V = V :=
  StatisticalRL.Analysis.contraction_exists_unique (M.valueBellman_contracting π)

/-- Selected only after the exact existence-and-uniqueness theorem. -/
noncomputable def valueFixedPoint (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : State → ℝ :=
  Classical.choose (M.value_fixedPoint_exists_unique π)

theorem valueFixedPoint_spec (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : M.valueBellman π (M.valueFixedPoint π) =
      M.valueFixedPoint π :=
  (Classical.choose_spec (M.value_fixedPoint_exists_unique π)).1

theorem valueFixedPoint_characterization (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) :
    M.valueBellman π V = V ↔ V = M.valueFixedPoint π := by
  constructor
  · intro hV
    exact (Classical.choose_spec (M.value_fixedPoint_exists_unique π)).2 V hV
  · intro hV
    rw [hV]
    exact M.valueFixedPoint_spec π

/-- Exact geometric error estimate for actual finite trajectory expectations. -/
theorem finiteDiscountedValue_error (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    ‖M.finiteDiscountedValue π n - M.valueFixedPoint π‖ ≤
      M.discount ^ n * ‖(0 : State → ℝ) - M.valueFixedPoint π‖ := by
  rw [M.finiteDiscountedValue_eq_iterate π n]
  simpa only [dist_eq_norm, coe_discountConstant] using
    StatisticalRL.Analysis.iterate_dist_le (M.valueBellman_lipschitz π)
      (M.valueFixedPoint_spec π) 0 n

/-- The expectations of the actual discounted finite path returns converge to
the unique Bellman state-value solution. Interchange with expectation on an
infinite path is not asserted here. -/
theorem tendsto_finiteDiscountedValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    Tendsto (M.finiteDiscountedValue π) atTop (𝓝 (M.valueFixedPoint π)) := by
  have heq := (M.valueBellman_contracting π).fixedPoint_unique (M.valueFixedPoint_spec π)
  have hseq : M.finiteDiscountedValue π = fun n ↦ (M.valueBellman π)^[n] 0 := by
    funext n
    exact M.finiteDiscountedValue_eq_iterate π n
  rw [hseq]
  simpa only [← heq] using
    (M.valueBellman_contracting π).tendsto_iterate_fixedPoint 0

end StatisticalRL.DiscountedMDP
