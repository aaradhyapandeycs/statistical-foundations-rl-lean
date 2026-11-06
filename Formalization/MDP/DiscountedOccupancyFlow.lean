import Formalization.MDP.DiscountedOccupancy

/-!
# Flow equation for the discounted state occupancy

The time-`t` state law is the `t`-fold forward push of the initial law under the policy
transition kernel, so the discounted state occupancy
`d(s) = (1-γ) ∑_t γ^t P(s_t = s)` (`eq:defn-dpi-occupancy-discounted-dist`) satisfies the flow
equation `d = (1-γ) ρ + γ dᵀ P_π`, i.e. `dᵀ (I - γ P_π) = (1-γ) ρᵀ`
(used as `eq:infinite-d-matrix-form` in the offline chapter).
-/

open scoped BigOperators

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- One more stationary stage pushes the current law forward by one step. -/
theorem stateAfter_replicate_succ (stage : DecisionStage State Action) (t : ℕ)
    (ρ : FiniteDistribution State) :
    DecisionStage.stateAfter (List.replicate (t + 1) stage) ρ =
      (DecisionStage.stateAfter (List.replicate t stage) ρ).bind
        (fun s ↦ (stage.policy s).bind (stage.transition s)) := by
  induction t generalizing ρ with
  | zero => simp [DecisionStage.stateAfter]
  | succ t ih =>
    have h := ih (ρ.bind (fun s ↦ (stage.policy s).bind (stage.transition s)))
    simp only [List.replicate_succ, DecisionStage.stateAfter] at h ⊢
    exact h

theorem occupancyStateLaw_eq_replicate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (t : ℕ) :
    M.occupancyStateLaw π ρ t =
      DecisionStage.stateAfter (List.replicate t (M.stationaryStage π)) ρ := by
  simp [occupancyStateLaw, occupancyStages, occupancyIndex, List.take_replicate]

theorem occupancyStateAt_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) :
    M.occupancyStateAt π ρ 0 s = ρ.prob s := by
  simp [occupancyStateAt, occupancyStateLaw_eq_replicate, DecisionStage.stateAfter]

theorem occupancyStateAt_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (t : ℕ) (s : State) :
    M.occupancyStateAt π ρ (t + 1) s =
      ∑ u, M.occupancyStateAt π ρ t u * (M.policyTransition π u).prob s := by
  rw [occupancyStateAt, occupancyStateLaw_eq_replicate, stateAfter_replicate_succ]
  simp [FiniteDistribution.bind, FiniteDistribution.expectation, occupancyStateAt,
    occupancyStateLaw_eq_replicate, policyTransition, stationaryStage]

/-- Flow equation: `d(s) = (1-γ) ρ(s) + γ ∑_u d(u) P_π(u, s)`. -/
theorem discountedStateOccupancy_flow (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State) (s : State) :
    M.discountedStateOccupancy π ρ s =
      (1 - M.discount) * ρ.prob s +
        M.discount * ∑ u, M.discountedStateOccupancy π ρ u * (M.policyTransition π u).prob s := by
  have hsum := M.discountedState_summable π ρ
  set γ := M.discount with hγ
  set T : State → ℝ := fun u ↦ ∑' t : ℕ, γ ^ t * M.occupancyStateAt π ρ t u with hT
  have hstep : ∀ t : ℕ, γ ^ (t + 1) * M.occupancyStateAt π ρ (t + 1) s =
      γ * ∑ u, (γ ^ t * M.occupancyStateAt π ρ t u) * (M.policyTransition π u).prob s := by
    intro t
    rw [occupancyStateAt_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    ring
  have hT_s : T s = ρ.prob s + γ * ∑ u, T u * (M.policyTransition π u).prob s := by
    rw [hT]
    simp only
    rw [(hsum s).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, occupancyStateAt_zero]
    simp_rw [hstep]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun u _ ↦ (hsum u).mul_right _)]
    simp_rw [tsum_mul_right]
  unfold discountedStateOccupancy
  change (1 - γ) * T s = (1 - γ) * ρ.prob s + γ * ∑ u, ((1 - γ) * T u) *
    (M.policyTransition π u).prob s
  rw [hT_s]
  have : ∑ u, ((1 - γ) * T u) * (M.policyTransition π u).prob s =
      (1 - γ) * ∑ u, T u * (M.policyTransition π u).prob s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    ring
  rw [this]
  ring

end StatisticalRL.DiscountedMDP
