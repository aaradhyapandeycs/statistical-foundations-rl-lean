import Formalization.MDP.PrefixValueBridge

/-!
# Deterministic policy-evaluation perturbation

The empirical and true MDPs may have arbitrary transition kernels, but share
known rewards, discount, and the evaluated stationary policy. Values are the
actual expectations under the respective infinite trajectory laws.
-/

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The empirical-minus-true policy-transition error applied to the true value. -/
noncomputable def policyValueResidual (M Mhat : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : State → ℝ := fun s ↦
  (Mhat.policyTransition π s).expectation (M.trajectoryExpectedValue π) -
    (M.policyTransition π s).expectation (M.trajectoryExpectedValue π)

/-- Exact Bellman difference identity for actual infinite-trajectory policy values. -/
theorem trajectoryValue_perturbation_identity (M Mhat : DiscountedMDP State Action)
    (π : StationaryPolicy State Action)
    (hr : Mhat.reward = M.reward) (hγ : Mhat.discount = M.discount) (s : State) :
    Mhat.trajectoryExpectedValue π s - M.trajectoryExpectedValue π s =
      M.discount * ((Mhat.policyTransition π s).expectation
        (Mhat.trajectoryExpectedValue π - M.trajectoryExpectedValue π) +
        policyValueResidual M Mhat π s) := by
  have ht := congrFun (M.valueFixedPoint_spec π) s
  have hh := congrFun (Mhat.valueFixedPoint_spec π) s
  rw [← M.trajectoryExpectedValue_eq_valueFixedPoint π] at ht
  rw [← Mhat.trajectoryExpectedValue_eq_valueFixedPoint π] at hh
  simp only [valueBellman] at ht hh
  rw [hr, hγ] at hh
  have hsub := (Mhat.policyTransition π s).expectation_sub
    (Mhat.trajectoryExpectedValue π) (M.trajectoryExpectedValue π)
  change (Mhat.policyTransition π s).expectation
      (Mhat.trajectoryExpectedValue π - M.trajectoryExpectedValue π) = _ at hsub
  simp only [policyValueResidual]
  rw [hsub]
  nlinarith only [ht, hh]

/-- The empirical Bellman residual at the true trajectory value is exactly
γ times the true-value transition residual. -/
theorem valueBellman_perturbation_residual (M Mhat : DiscountedMDP State Action)
    (π : StationaryPolicy State Action)
    (hr : Mhat.reward = M.reward) (hγ : Mhat.discount = M.discount) :
    Mhat.valueBellman π (M.trajectoryExpectedValue π) -
      M.valueBellman π (M.trajectoryExpectedValue π) =
        M.discount • policyValueResidual M Mhat π := by
  funext s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, valueBellman, policyValueResidual]
  rw [hr, hγ]
  ring

/-- Deterministic perturbation bound in the state sup norm, with the exact
policy-induced residual on the true trajectory value. -/
theorem trajectoryValue_perturbation_bound (M Mhat : DiscountedMDP State Action)
    (π : StationaryPolicy State Action)
    (hr : Mhat.reward = M.reward) (hγ : Mhat.discount = M.discount) :
    ‖Mhat.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ ≤
      M.discount * ‖policyValueResidual M Mhat π‖ / (1 - M.discount) := by
  let V := M.trajectoryExpectedValue π
  let W := Mhat.trajectoryExpectedValue π
  have ht : M.valueBellman π V = V := by
    dsimp [V]
    rw [M.trajectoryExpectedValue_eq_valueFixedPoint]
    exact M.valueFixedPoint_spec π
  have hh : Mhat.valueBellman π W = W := by
    dsimp [W]
    rw [Mhat.trajectoryExpectedValue_eq_valueFixedPoint]
    exact Mhat.valueFixedPoint_spec π
  have hdecomp : W - V = (Mhat.valueBellman π W - Mhat.valueBellman π V) +
      (Mhat.valueBellman π V - M.valueBellman π V) := by
    rw [hh, ht]
    abel
  have hcon := Mhat.norm_valueBellman_sub_le π W V
  rw [hγ] at hcon
  have hres : Mhat.valueBellman π V - M.valueBellman π V =
      M.discount • policyValueResidual M Mhat π :=
    valueBellman_perturbation_residual M Mhat π hr hγ
  have hbound : ‖W - V‖ ≤ M.discount * ‖W - V‖ +
      M.discount * ‖policyValueResidual M Mhat π‖ := by
    calc
      ‖W - V‖ ≤ ‖Mhat.valueBellman π W - Mhat.valueBellman π V‖ +
          ‖Mhat.valueBellman π V - M.valueBellman π V‖ := by
        rw [hdecomp]
        exact norm_add_le _ _
      _ ≤ M.discount * ‖W - V‖ + M.discount * ‖policyValueResidual M Mhat π‖ := by
        rw [hres, norm_smul, Real.norm_eq_abs, abs_of_nonneg M.discount_nonneg]
        exact add_le_add hcon le_rfl
  have hpos : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  change ‖W - V‖ ≤ M.discount * ‖policyValueResidual M Mhat π‖ / (1 - M.discount)
  apply (le_div_iff₀ hpos).2
  nlinarith only [hbound]

/-- A uniform pointwise residual estimate yields the corresponding actual
trajectory policy-evaluation error bound. -/
theorem trajectoryValue_perturbation_bound_of_residual (M Mhat : DiscountedMDP State Action)
    (π : StationaryPolicy State Action)
    (hr : Mhat.reward = M.reward) (hγ : Mhat.discount = M.discount)
    (ε : ℝ) (hε : 0 ≤ ε) (hres : ∀ s, |policyValueResidual M Mhat π s| ≤ ε) :
    ‖Mhat.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ ≤
      M.discount * ε / (1 - M.discount) := by
  have hnorm : ‖policyValueResidual M Mhat π‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).2
    intro s
    simpa only [Real.norm_eq_abs] using hres s
  calc
    _ ≤ M.discount * ‖policyValueResidual M Mhat π‖ / (1 - M.discount) :=
      trajectoryValue_perturbation_bound M Mhat π hr hγ
    _ ≤ M.discount * ε / (1 - M.discount) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm M.discount_nonneg)
        (sub_nonneg.mpr M.discount_lt_one.le)


/-- At zero discount, identical rewards give identical trajectory values for
any two transition kernels. -/
theorem trajectoryValue_eq_of_zero_discount (M Mhat : DiscountedMDP State Action)
    (π : StationaryPolicy State Action)
    (hr : Mhat.reward = M.reward) (hγ : Mhat.discount = M.discount)
    (hzero : M.discount = 0) :
    Mhat.trajectoryExpectedValue π = M.trajectoryExpectedValue π := by
  have hb := trajectoryValue_perturbation_bound M Mhat π hr hγ
  simp only [hzero, zero_mul, zero_div] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

end StatisticalRL.DiscountedMDP
