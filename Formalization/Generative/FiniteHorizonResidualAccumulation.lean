import Formalization.Generative.FiniteHorizonPolicyPerturbation
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Deterministic accumulation of actual finite suffix transition residuals.
No policy independence or statistical sample-complexity bound is assumed. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual row-residual norms at each remaining stage, on the comparison
model's actual policy continuation value, in chronological order. -/
noncomputable def policyResidualCharges :
    List (EnvironmentStage State Action × EnvironmentStage State Action) →
      (ℕ → StationaryPolicy State Action) → List ℝ
  | [], _ => []
  | (E,F) :: tail, π =>
      ‖policyRowResidual E F
        (DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.snd)
          (fun k ↦ π (k + 1))))‖ :: policyResidualCharges tail (fun k ↦ π (k + 1))

theorem policyResidualCharges_length
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) :
    (policyResidualCharges pairs π).length = pairs.length := by
  induction pairs generalizing π with
  | nil => rfl
  | cons p tail ih => rcases p with ⟨E,F⟩; simpa only [policyResidualCharges, List.length_cons] using congrArg Nat.succ (ih _)

theorem policyResidualCharges_sum_nonneg
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) : 0 ≤ (policyResidualCharges pairs π).sum := by
  induction pairs generalizing π with
  | nil => exact le_rfl
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    exact add_nonneg (norm_nonneg _) (ih _)

/-- True kernels and policy averaging do not amplify a uniform future-error
bound, so the explicit finite residual charges accumulate additively. -/
theorem propagatedPolicyResidual_abs_le_charges
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (s : State) :
    |propagatedPolicyResidual pairs π s| ≤ (policyResidualCharges pairs π).sum := by
  induction pairs generalizing π s with
  | nil => simp [propagatedPolicyResidual, policyResidualCharges]
  | cons p tail ih =>
    rcases p with ⟨E,F⟩
    let R := policyRowResidual E F
      (DecisionStage.trajectoryValue (EnvironmentStage.controlled (tail.map Prod.snd) (fun k ↦ π (k + 1))))
    change |(π 0 s).expectation (fun a ↦ R s a + (E.transition s a).expectation
      (propagatedPolicyResidual tail (fun k ↦ π (k + 1))))| ≤
      ‖R‖ + (policyResidualCharges tail (fun k ↦ π (k + 1))).sum
    apply (π 0 s).abs_expectation_le
    intro a
    have hr : |R s a| ≤ ‖R‖ := by
      have hh := (norm_le_pi_norm (R s) a).trans (norm_le_pi_norm R s)
      simpa only [Real.norm_eq_abs] using hh
    exact (abs_add_le _ _).trans (add_le_add hr ((E.transition s a).abs_expectation_le (fun t ↦ ih _ t)))

theorem propagatedPolicyResidual_norm_le_charges
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) :
    ‖propagatedPolicyResidual pairs π‖ ≤ (policyResidualCharges pairs π).sum := by
  apply (pi_norm_le_iff_of_nonneg (policyResidualCharges_sum_nonneg pairs π)).2
  intro s
  simpa only [Real.norm_eq_abs] using propagatedPolicyResidual_abs_le_charges pairs π s

/-- Actual finite policy evaluation error is controlled by actual transition
residual charges; reward equality is the source's known-reward convention. -/
theorem trajectoryValue_difference_norm_le_charges
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action)
    (hr : ∀ p ∈ pairs, p.2.reward = p.1.reward) :
    ‖DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.snd) π) -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π)‖ ≤
      (policyResidualCharges pairs π).sum := by
  have he : (DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.snd) π) -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (pairs.map Prod.fst) π)) =
      propagatedPolicyResidual pairs π := by
    funext s
    exact trajectoryValue_difference_eq_propagatedResidual pairs π hr s
  rw [he]
  exact propagatedPolicyResidual_norm_le_charges pairs π

/-- A uniform bound on row-residual charges yields one horizon factor. -/
theorem policyResidualCharges_sum_le_uniform
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (r : ℝ)
    (hc : ∀ c ∈ policyResidualCharges pairs π, c ≤ r) :
    (policyResidualCharges pairs π).sum ≤ pairs.length * r := by
  have hp := List.sum_le_card_nsmul (policyResidualCharges pairs π) r hc
  simpa only [policyResidualCharges_length, nsmul_eq_mul] using hp

/-- Same-data empirical policy evaluation, for any nonstationary policy,
including a realized data-dependent choice as a deterministic application. -/
theorem empiricalTrajectoryValue_norm_le_charges {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) (π : ℕ → StationaryPolicy State Action) :
    ‖DecisionStage.trajectoryValue (EnvironmentStage.controlled (empiricalStages E N hN data) π) -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E) π)‖ ≤
      (policyResidualCharges (pairedEmpiricalStages E N hN data) π).sum := by
  have he : (DecisionStage.trajectoryValue (EnvironmentStage.controlled (empiricalStages E N hN data) π) -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E) π)) =
      propagatedPolicyResidual (pairedEmpiricalStages E N hN data) π := by
    funext s
    exact empiricalTrajectoryValue_difference_eq_residual E N hN data π s
  rw [he]
  exact propagatedPolicyResidual_norm_le_charges _ π

/-- Deterministic H·r error bound once a common event controls each actual
suffix charge. This theorem supplies no such event or independence premise. -/
theorem empiricalTrajectoryValue_norm_le_uniform {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action H N) (π : ℕ → StationaryPolicy State Action) (r : ℝ)
    (hc : ∀ c ∈ policyResidualCharges (pairedEmpiricalStages E N hN data) π, c ≤ r) :
    ‖DecisionStage.trajectoryValue (EnvironmentStage.controlled (empiricalStages E N hN data) π) -
      DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E) π)‖ ≤ H * r := by
  apply (empiricalTrajectoryValue_norm_le_charges E N hN data π).trans
  simpa only [pairedEmpiricalStages, List.length_ofFn] using
    policyResidualCharges_sum_le_uniform (pairedEmpiricalStages E N hN data) π r hc

end StatisticalRL.FiniteHorizonGenerative
