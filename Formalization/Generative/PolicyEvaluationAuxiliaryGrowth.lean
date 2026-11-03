import Formalization.Generative.PolicyEvaluationGeneralForcing
import Formalization.Generative.PolicyEvaluationAuxiliary

/-! Source auxiliary-value growth from the general-forcing variance bound. -/

open scoped Matrix

namespace StatisticalRL.ModelBasedPolicyEvaluation

open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance growthStateDecidable : DecidableEq State := Classical.decEq State

/-- At every level the square-root variance resolvent obeys the stronger
scaled bound with constant one, including zero discount. -/
theorem auxiliaryValue_succ_scaled_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) :
    M.discount * ‖auxiliaryValue M π (l + 1)‖ ≤
      ‖auxiliaryValue M π l‖ / Real.sqrt (1 - M.discount) := by
  have h := M.forcingPolicyValue_varianceResolvent_bound π (auxiliaryReward M π l)
    (auxiliaryReward_nonneg M π l)
  have hV : M.forcingPolicyValue π (auxiliaryReward M π l) = auxiliaryValue M π l :=
    auxiliaryValue_eq_inverse M π l
  rw [hV] at h
  exact h

/-- Positive-discount one-step growth, with constant one instead of √2. -/
theorem auxiliaryValue_succ_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) (hγ : 0 < M.discount) :
    ‖auxiliaryValue M π (l + 1)‖ ≤
      (1 / (M.discount * Real.sqrt (1 - M.discount))) * ‖auxiliaryValue M π l‖ := by
  have hs : 0 < Real.sqrt (1 - M.discount) := Real.sqrt_pos.2 (sub_pos.mpr M.discount_lt_one)
  have h := auxiliaryValue_succ_scaled_bound M π l
  calc
    _ ≤ (‖auxiliaryValue M π l‖ / Real.sqrt (1 - M.discount)) / M.discount :=
      (le_div_iff₀ hγ).2 (by simpa only [mul_comm] using h)
    _ = _ := by ring

/-- The improved geometric bound for all auxiliary levels. -/
theorem auxiliaryValue_norm_growth_sharp (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) (hγ : 0 < M.discount) :
    ‖auxiliaryValue M π l‖ ≤
      (1 / (M.discount * Real.sqrt (1 - M.discount))) ^ l *
        ‖M.trajectoryExpectedValue π‖ := by
  have hc : 0 ≤ 1 / (M.discount * Real.sqrt (1 - M.discount)) := by positivity
  induction l with
  | zero => simp [auxiliaryValue]
  | succ l ih =>
    calc
      _ ≤ (1 / (M.discount * Real.sqrt (1 - M.discount))) * ‖auxiliaryValue M π l‖ :=
        auxiliaryValue_succ_bound M π l hγ
      _ ≤ (1 / (M.discount * Real.sqrt (1 - M.discount))) *
          ((1 / (M.discount * Real.sqrt (1 - M.discount))) ^ l *
            ‖M.trajectoryExpectedValue π‖) := mul_le_mul_of_nonneg_left ih hc
      _ = _ := by rw [pow_succ]; ring

/-- The source's factor √2 follows from the stronger constant-one bound. -/
theorem auxiliaryValue_norm_growth_source (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) (hγ : 0 < M.discount) :
    ‖auxiliaryValue M π l‖ ≤
      (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ l *
        ‖M.trajectoryExpectedValue π‖ := by
  have hs : 0 < M.discount * Real.sqrt (1 - M.discount) :=
    mul_pos hγ (Real.sqrt_pos.2 (sub_pos.mpr M.discount_lt_one))
  have htwo : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hbase : 1 / (M.discount * Real.sqrt (1 - M.discount)) ≤
      Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount)) :=
    div_le_div_of_nonneg_right htwo hs.le
  have hp := pow_le_pow_left₀ (div_nonneg zero_le_one hs.le) hbase l
  exact (auxiliaryValue_norm_growth_sharp M π l hγ).trans
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _))

/-- The source's explicit horizon-only geometric bound. -/
theorem auxiliaryValue_norm_growth_source_uniform (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) (hγ : 0 < M.discount) :
    ‖auxiliaryValue M π l‖ ≤
      (1 / (1 - M.discount)) *
        (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ l := by
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hV : ‖M.trajectoryExpectedValue π‖ ≤ 1 / (1 - M.discount) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro s
    have hv := M.trajectoryExpectedValue_bounds π s
    rw [Real.norm_eq_abs, abs_of_nonneg hv.1]
    exact hv.2
  have hfactor : 0 ≤ (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ l := by positivity
  calc
    _ ≤ (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ l *
        ‖M.trajectoryExpectedValue π‖ := auxiliaryValue_norm_growth_source M π l hγ
    _ ≤ (Real.sqrt 2 / (M.discount * Real.sqrt (1 - M.discount))) ^ l *
        (1 / (1 - M.discount)) := mul_le_mul_of_nonneg_left hV hfactor
    _ = _ := by ring

/-- At zero discount, the true and empirical auxiliary values coincide at
all levels and for every realization of the data. -/
theorem auxiliaryValue_empirical_eq_of_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (l : ℕ) (hγ : M.discount = 0) :
    empiricalAuxiliaryValue M π N hN data l = auxiliaryValue M π l := by
  have h := auxiliaryValue_eq_inverse M π l
  simp only [hγ, zero_smul, sub_zero, inv_one, Matrix.one_mulVec] at h
  unfold empiricalAuxiliaryValue
  simp only [hγ, zero_smul, sub_zero, inv_one, Matrix.one_mulVec]
  exact h

end StatisticalRL.ModelBasedPolicyEvaluation
