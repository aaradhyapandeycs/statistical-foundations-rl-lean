import Formalization.MDP.FixedPoint
import Formalization.MDP.PolicyIteration

/-! Iteration counts read from the linear convergence of value iteration and policy
iteration (prose after Lemma 2.1, `chapters/prelim.tex:357–360`). -/

namespace StatisticalRL

/-- If `log(D/ε)/(1−γ) ≤ k` with `0 ≤ γ < 1`, `D ≥ 0` and `ε > 0`, then `γ^k D ≤ ε`.
For `D = 0` this is trivial; otherwise `γ^k ≤ exp(−(1−γ)k) ≤ exp(−log(D/ε)) = ε/D`. -/
theorem discount_pow_mul_le_of_log_div_le (γ D ε : ℝ) (k : ℕ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hD : 0 ≤ D) (hε : 0 < ε) (hk : Real.log (D / ε) / (1 - γ) ≤ k) :
    γ ^ k * D ≤ ε := by
  rcases hD.eq_or_lt with rfl | hDpos
  · simpa using hε.le
  have hh : 0 < 1 - γ := sub_pos.mpr hγ1
  have hexp : γ ≤ Real.exp (γ - 1) := by
    have := Real.add_one_le_exp (γ - 1)
    linarith
  have hpow : γ ^ k ≤ Real.exp (γ - 1) ^ k := pow_le_pow_left₀ hγ hexp k
  rw [← Real.exp_nat_mul] at hpow
  have hk' : Real.log (D / ε) ≤ k * (1 - γ) := (div_le_iff₀ hh).1 hk
  have hle : γ ^ k ≤ ε / D := by
    calc
      γ ^ k ≤ Real.exp (k * (γ - 1)) := hpow
      _ ≤ Real.exp (-Real.log (D / ε)) := Real.exp_le_exp.mpr (by linarith)
      _ = ε / D := by
        rw [Real.exp_neg, Real.exp_log (div_pos hDpos hε), inv_div]
  calc
    γ ^ k * D ≤ ε / D * D := mul_le_mul_of_nonneg_right hle hDpos.le
    _ = ε := div_mul_cancel₀ ε hDpos.ne'

namespace DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Value iteration: `k ≥ log(‖Q₀ − Q⋆‖∞/ε)/(1−γ)` iterations give `‖Q_k − Q⋆‖∞ ≤ ε`. -/
theorem value_iteration_count (M : DiscountedMDP State Action) (ε : ℝ) (hε : 0 < ε)
    (Q₀ : State → Action → ℝ) (k : ℕ)
    (hk : Real.log (‖Q₀ - M.optimalityFixedPoint‖ / ε) / (1 - M.discount) ≤ k) :
    ‖M.qOptimality^[k] Q₀ - M.optimalityFixedPoint‖ ≤ ε :=
  (M.value_iteration_error Q₀ k).trans
    (discount_pow_mul_le_of_log_div_le _ _ _ k M.discount_nonneg M.discount_lt_one
      (norm_nonneg _) hε hk)

/-- Policy iteration with arbitrary greedy ties: `k ≥ log(‖Q^{π₀} − Q⋆‖∞/ε)/(1−γ)`
iterations give `‖Q^{π_k} − Q⋆‖∞ ≤ ε`. -/
theorem arbitraryGreedyPolicyIteration_count (M : DiscountedMDP State Action) (ε : ℝ)
    (hε : 0 < ε) (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s))
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.policyFixedPoint (π n) s (f n s) = actionMaximum (M.policyFixedPoint (π n) s))
    (k : ℕ)
    (hk : Real.log (‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖ / ε) /
      (1 - M.discount) ≤ k) :
    ‖M.policyFixedPoint (π k) - M.optimalityFixedPoint‖ ≤ ε :=
  (M.arbitraryGreedyPolicyIteration_error π f hupdate hmax k).trans
    (discount_pow_mul_le_of_log_div_le _ _ _ k M.discount_nonneg M.discount_lt_one
      (norm_nonneg _) hε hk)

end DiscountedMDP

end StatisticalRL
