import Formalization.MDP.OccupancyBridge
import Formalization.MDP.PrefixValueBridge
import Mathlib.Analysis.SpecificLimits.Basic

/-! Discounted state and state-action occupancy for actual controlled paths.
Source: arXiv:2610.41903v1, `eq:defn-dpi-occupancy-discounted-dist`. -/

open scoped BigOperators Topology
open MeasureTheory Filter

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The trajectory stages through and including decision time `t`. -/
def occupancyStages (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (t : ℕ) : List (DecisionStage State Action) :=
  List.replicate (t + 1) (M.stationaryStage π)

/-- The actual zero-based time `t` in its finite prefix. -/
def occupancyIndex (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (t : ℕ) : Fin (M.occupancyStages π t).length := ⟨t, by simp [occupancyStages]⟩

/-- Probability law of the state just before the decision at time `t`. -/
def occupancyStateLaw (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (t : ℕ) : FiniteDistribution State :=
  DecisionStage.stateAfter ((M.occupancyStages π t).take (M.occupancyIndex π t).val) ρ

/-- The state event at time `t`, under the actual prefix law and initial law. -/
def occupancyStateAt (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (t : ℕ) (s : State) : ℝ :=
  (M.occupancyStateLaw π ρ t).prob s

/-- The state-action event at time `t`, under the actual controlled law. -/
noncomputable def occupancyJointAt (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (t : ℕ) (s : State) (a : Action) : ℝ :=
  DecisionStage.stateActionOccupancy (M.occupancyStages π t) ρ (M.occupancyIndex π t) s a

/-- Timewise joint probabilities factor by the actual stationary policy. -/
theorem occupancyJointAt_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (t : ℕ) (s : State) (a : Action) :
    M.occupancyJointAt π ρ t s a = M.occupancyStateAt π ρ t s * (π s).prob a := by
  rw [occupancyJointAt, DecisionStage.stateActionOccupancy_eq]
  simp [occupancyStateAt, occupancyStateLaw, occupancyStages, occupancyIndex,
    DecisionStage.stateOccupancy, stationaryStage]

theorem finiteDistribution_prob_le_one {Ω : Type*} [Fintype Ω]
    (d : FiniteDistribution Ω) (x : Ω) : d.prob x ≤ 1 := by
  calc
    d.prob x ≤ ∑ y, d.prob y := Finset.single_le_sum (fun y _ ↦ d.prob_nonneg y) (Finset.mem_univ x)
    _ = 1 := d.sum_prob

theorem occupancyStateAt_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (t : ℕ) (s : State) : 0 ≤ M.occupancyStateAt π ρ t s :=
  (M.occupancyStateLaw π ρ t).prob_nonneg s

theorem occupancyStateAt_le_one (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (t : ℕ) (s : State) : M.occupancyStateAt π ρ t s ≤ 1 :=
  finiteDistribution_prob_le_one _ s

/-- State occupancy is the normalized geometrically weighted state event sum. -/
noncomputable def discountedStateOccupancy (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) : ℝ :=
  (1 - M.discount) * ∑' t : ℕ, M.discount ^ t * M.occupancyStateAt π ρ t s

/-- State-action occupancy is the corresponding sum of genuine joint events. -/
noncomputable def discountedJointOccupancy (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) (a : Action) : ℝ :=
  (1 - M.discount) * ∑' t : ℕ, M.discount ^ t * M.occupancyJointAt π ρ t s a

theorem discountedState_summable (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (s : State) :
    Summable (fun t : ℕ ↦ M.discount ^ t * M.occupancyStateAt π ρ t s) := by
  apply Summable.of_nonneg_of_le
  · intro t; exact mul_nonneg (pow_nonneg M.discount_nonneg _) (M.occupancyStateAt_nonneg π ρ t s)
  · intro t
    simpa using mul_le_mul_of_nonneg_left (M.occupancyStateAt_le_one π ρ t s)
      (pow_nonneg M.discount_nonneg t)
  · exact summable_geometric_of_lt_one M.discount_nonneg M.discount_lt_one

/-- The source's stationary joint factorization follows from every timewise event. -/
theorem discountedJointOccupancy_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) (a : Action) :
    M.discountedJointOccupancy π ρ s a =
      M.discountedStateOccupancy π ρ s * (π s).prob a := by
  unfold discountedJointOccupancy discountedStateOccupancy
  simp_rw [M.occupancyJointAt_eq, ← mul_assoc, tsum_mul_right]
  ring

/-- Discounted state occupancy is nonnegative and sums to one. -/
theorem discountedStateOccupancy_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) :
    0 ≤ M.discountedStateOccupancy π ρ s := by
  apply mul_nonneg (sub_nonneg.mpr M.discount_lt_one.le)
  exact tsum_nonneg (fun t ↦ mul_nonneg (pow_nonneg M.discount_nonneg t)
    (M.occupancyStateAt_nonneg π ρ t s))

theorem discountedStateOccupancy_sum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) :
    ∑ s, M.discountedStateOccupancy π ρ s = 1 := by
  simp only [discountedStateOccupancy, ← Finset.mul_sum]
  rw [← Summable.tsum_finsetSum (fun s _ ↦ M.discountedState_summable π ρ s)]
  simp_rw [← Finset.mul_sum]
  simp only [occupancyStateAt, FiniteDistribution.sum_prob, mul_one]
  rw [tsum_geometric_of_lt_one M.discount_nonneg M.discount_lt_one]
  have h : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  field_simp

/-- The sum over actions is the discounted state occupancy. -/
theorem discountedJointOccupancy_sum_action (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) :
    ∑ a, M.discountedJointOccupancy π ρ s a = M.discountedStateOccupancy π ρ s := by
  simp_rw [M.discountedJointOccupancy_eq, ← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]

/-- The discounted joint occupancy is a normalized probability law. -/
theorem discountedJointOccupancy_sum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) :
    ∑ s, ∑ a, M.discountedJointOccupancy π ρ s a = 1 := by
  simp [M.discountedJointOccupancy_sum_action, M.discountedStateOccupancy_sum]

local instance discountedOccupancyStateMeasurable : MeasurableSpace State := ⊤
local instance discountedOccupancyActionMeasurable : MeasurableSpace Action := ⊤
noncomputable local instance discountedOccupancyStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance discountedOccupancyActionDecidable : DecidableEq Action := Classical.decEq Action

private theorem finiteOccupancy_integral {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    d.expectation f = ∫ x, f x ∂d.toPMF.toMeasure := by
  rw [PMF.integral_eq_sum]
  simp [FiniteDistribution.expectation, FiniteDistribution.toPMF_apply,
    ENNReal.toReal_ofReal, d.prob_nonneg]

/-- The finite-prefix state projection is the source-time state on the
original infinite path. -/
theorem finitePrefix_pathState_eq (stages : List (DecisionStage State Action))
    (i : Fin stages.length) (x : State) (path : ℕ → Action × State) :
    DecisionStage.pathState stages.length i x (finitePrefix stages path) =
      trajectoryState x path i.val := by
  induction stages generalizing x path with
  | nil => exact Fin.elim0 i
  | cons stage tail ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp only [List.length_cons, DecisionStage.pathState, Fin.cases_succ]
      rw [finitePrefix_cons_tail]
      have hh := finitePrefix_cons_head stage tail path
      have hs := congrArg Prod.snd hh
      simp only at hs
      rw [hs, ih j]
      cases h : j.val with
      | zero => simp [trajectoryState, h]
      | succ n => simp [trajectoryState, h]

/-- The finite-prefix action projection is the source-time action on the
original infinite path. -/
theorem finitePrefix_pathAction_eq (stages : List (DecisionStage State Action))
    (i : Fin stages.length) (path : ℕ → Action × State) :
    DecisionStage.pathAction stages.length i (finitePrefix stages path) = (path i.val).1 := by
  induction stages generalizing path with
  | nil => exact Fin.elim0 i
  | cons stage tail ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hh := finitePrefix_cons_head stage tail path
      exact congrArg Prod.fst hh
    · simp only [List.length_cons, DecisionStage.pathAction, Fin.cases_succ]
      rw [finitePrefix_cons_tail, ih j]
      rfl

/-- Each state time-marginal is the actual infinite-path event, with the
initial distribution explicitly averaged over its possible starting states. -/
theorem occupancyStateAt_eq_infinitePath (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (t : ℕ) (s : State) :
    M.occupancyStateAt π ρ t s = ρ.expectation (fun x ↦
      ∫ path, if DecisionStage.pathState (M.occupancyStages π t).length
        (M.occupancyIndex π t) x (finitePrefix (M.occupancyStages π t) path) = s
        then (1 : ℝ) else 0 ∂M.infiniteTrajectoryLaw π x) := by
  change DecisionStage.stateOccupancy (M.occupancyStages π t) ρ (M.occupancyIndex π t) s = _
  rw [DecisionStage.stateOccupancy_eq_fullPath]
  apply congrArg ρ.expectation
  funext x
  have hs : ∀ z ∈ M.occupancyStages π t, z = M.stationaryStage π := by
    intro z hz
    exact (List.mem_replicate.mp hz).2
  rw [finiteOccupancy_integral, ← M.infiniteTrajectoryLaw_map_finitePrefix π _ hs x]
  exact integral_map (measurable_finitePrefix _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Each state-action time-marginal is the corresponding event under the
actual infinite trajectory law, averaged over the initial distribution. -/
theorem occupancyJointAt_eq_infinitePath (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (t : ℕ) (s : State) (a : Action) :
    M.occupancyJointAt π ρ t s a = ρ.expectation (fun x ↦
      ∫ path, if DecisionStage.pathState (M.occupancyStages π t).length
        (M.occupancyIndex π t) x (finitePrefix (M.occupancyStages π t) path) = s ∧
        DecisionStage.pathAction (M.occupancyStages π t).length
          (M.occupancyIndex π t) (finitePrefix (M.occupancyStages π t) path) = a
        then (1 : ℝ) else 0 ∂M.infiniteTrajectoryLaw π x) := by
  unfold occupancyJointAt
  rw [DecisionStage.stateActionOccupancy_eq_fullPath]
  apply congrArg ρ.expectation
  funext x
  have hs : ∀ z ∈ M.occupancyStages π t, z = M.stationaryStage π := by
    intro z hz
    exact (List.mem_replicate.mp hz).2
  rw [finiteOccupancy_integral, ← M.infiniteTrajectoryLaw_map_finitePrefix π _ hs x]
  exact integral_map (measurable_finitePrefix _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- The state marginal is the probability of the source's actual `s_t` event. -/
theorem occupancyStateAt_eq_sourceEvent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (t : ℕ) (s : State) :
    M.occupancyStateAt π ρ t s = ρ.expectation (fun x ↦
      (M.infiniteTrajectoryLaw π x).real {path | trajectoryState x path t = s}) := by
  rw [M.occupancyStateAt_eq_infinitePath π ρ t s]
  apply congrArg ρ.expectation
  funext x
  simp_rw [finitePrefix_pathState_eq]
  change (∫ path, if trajectoryState x path t = s then (1 : ℝ) else 0
      ∂M.infiniteTrajectoryLaw π x) = _
  have hs : MeasurableSet {path : ℕ → Action × State | trajectoryState x path t = s} :=
    (measurable_trajectoryState x t) (measurableSet_singleton s)
  simpa [Set.indicator] using (integral_indicator_one hs)

/-- The joint marginal is the probability of the source's actual `(s_t,a_t)` event. -/
theorem occupancyJointAt_eq_sourceEvent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (t : ℕ) (s : State) (a : Action) :
    M.occupancyJointAt π ρ t s a = ρ.expectation (fun x ↦
      (M.infiniteTrajectoryLaw π x).real {path | trajectoryState x path t = s ∧ (path t).1 = a}) := by
  rw [M.occupancyJointAt_eq_infinitePath π ρ t s a]
  apply congrArg ρ.expectation
  funext x
  simp_rw [finitePrefix_pathState_eq, finitePrefix_pathAction_eq]
  change (∫ path, if trajectoryState x path t = s ∧ (path t).1 = a then (1 : ℝ) else 0
      ∂M.infiniteTrajectoryLaw π x) = _
  have hs : MeasurableSet {path : ℕ → Action × State | trajectoryState x path t = s} :=
    (measurable_trajectoryState x t) (measurableSet_singleton s)
  have ha : MeasurableSet {path : ℕ → Action × State | (path t).1 = a} := by
    have hm : Measurable (fun path : ℕ → Action × State ↦ (path t).1) := (measurable_pi_apply t).fst
    exact hm (measurableSet_singleton a)
  have h := integral_indicator_one (μ := M.infiniteTrajectoryLaw π x) (hs.inter ha)
  simpa [Set.indicator, Set.mem_inter_iff] using h

/-- The source state formula is the geometric sum of actual infinite-path
probabilities, mixed over the actual initial distribution. -/
theorem discountedStateOccupancy_eq_source (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) :
    M.discountedStateOccupancy π ρ s = (1 - M.discount) *
      ∑' t : ℕ, M.discount ^ t * ρ.expectation (fun x ↦
        (M.infiniteTrajectoryLaw π x).real {path | trajectoryState x path t = s}) := by
  simp only [discountedStateOccupancy, M.occupancyStateAt_eq_sourceEvent]

/-- The source joint formula is the geometric sum of actual infinite-path
state-action event probabilities, with the same initial distribution. -/
theorem discountedJointOccupancy_eq_source (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) (a : Action) :
    M.discountedJointOccupancy π ρ s a = (1 - M.discount) *
      ∑' t : ℕ, M.discount ^ t * ρ.expectation (fun x ↦
        (M.infiniteTrajectoryLaw π x).real {path | trajectoryState x path t = s ∧ (path t).1 = a}) := by
  simp only [discountedJointOccupancy, M.occupancyJointAt_eq_sourceEvent]

/-- Every deterministic stationary policy gives the source indicator formula;
this applies in particular to an optimal deterministic policy. -/
theorem discountedJointOccupancy_deterministic (M : DiscountedMDP State Action)
    (f : State → Action) (ρ : FiniteDistribution State) (s : State) (a : Action) :
    M.discountedJointOccupancy (fun x ↦ EnvironmentStage.pointMass (f x)) ρ s a =
      M.discountedStateOccupancy (fun x ↦ EnvironmentStage.pointMass (f x)) ρ s *
        (if a = f s then 1 else 0) := by
  rw [M.discountedJointOccupancy_eq]
  rfl

/-- Joint occupancy is nonnegative. -/
theorem discountedJointOccupancy_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) (a : Action) :
    0 ≤ M.discountedJointOccupancy π ρ s a := by
  rw [M.discountedJointOccupancy_eq]
  exact mul_nonneg (M.discountedStateOccupancy_nonneg π ρ s) ((π s).prob_nonneg a)

/-- The source's discounted state occupancy as a normalized finite distribution. -/
noncomputable def discountedStateLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) : FiniteDistribution State where
  prob := M.discountedStateOccupancy π ρ
  prob_nonneg := M.discountedStateOccupancy_nonneg π ρ
  sum_prob := M.discountedStateOccupancy_sum π ρ

/-- The source's discounted joint occupancy as a normalized finite distribution. -/
noncomputable def discountedJointLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) : FiniteDistribution (State × Action) where
  prob p := M.discountedJointOccupancy π ρ p.1 p.2
  prob_nonneg p := M.discountedJointOccupancy_nonneg π ρ p.1 p.2
  sum_prob := by
    rw [Fintype.sum_prod_type]
    exact M.discountedJointOccupancy_sum π ρ

/-- At zero discount, the source state occupancy is the initial law. -/
theorem discountedStateOccupancy_discount_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State)
    (hγ : M.discount = 0) : M.discountedStateOccupancy π ρ s = ρ.prob s := by
  unfold discountedStateOccupancy
  have hsum : (∑' t : ℕ, M.discount ^ t * M.occupancyStateAt π ρ t s) = ρ.prob s := by
    rw [tsum_eq_single 0]
    · simp [occupancyStateAt, occupancyStateLaw, occupancyStages, occupancyIndex,
        DecisionStage.stateAfter]
    · intro n hn
      cases n with
      | zero => exact (hn rfl).elim
      | succ n => simp [hγ]
  rw [hsum, hγ]
  simp

/-- At zero discount, the joint occupancy samples the initial action from π. -/
theorem discountedJointOccupancy_discount_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) (a : Action)
    (hγ : M.discount = 0) : M.discountedJointOccupancy π ρ s a = ρ.prob s * (π s).prob a := by
  rw [M.discountedJointOccupancy_eq, M.discountedStateOccupancy_discount_zero π ρ s hγ]

end StatisticalRL.DiscountedMDP
