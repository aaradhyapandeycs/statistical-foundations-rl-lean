import Formalization.Generative.GenerativeLowerBoundTheorem37Fin
import Formalization.MDP.PolicyValueQ
import Formalization.MDP.PrefixValueBridge
import Formalization.MDP.ForcedPrefixBridge

/-!
# Burn-in necessity, `N ≳ 1/(1−γ)` (`eq:sample-size-range-planning`)

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:934–940`. The prose says that
the sample-size condition `N ≥ Ω̃(1/(1−γ))` is necessary "for learning a policy that performs
strictly better than a random guess". The book does not define "random guess". This module proves
the following restricted reading, as a corollary of the corrected Theorem 3.7 lower bound
(`theorem37_corrected_fin_carriers`) at accuracy `ε = 1/(64(1−γ))`:

for `S ≥ 2`, `A ≥ 2`, `SA ≥ 16`, `γ ∈ [2/3, 1)` and `N ≤ log(SA)/(8(1−γ))`, every deterministic
policy estimator (a function of the known rewards, the known discount and the sample array) has,
on some MDP with discount `γ`, value gap `‖V⋆ − V^{π̂}‖∞ > 1/(64(1−γ))` with probability at least
`1/4`.

The transfer from the Q-metric of Theorem 3.7 to the value metric is
`‖Q^π − Q^{π'}‖∞ ≤ γ ‖V^π − V^{π'}‖∞ ≤ ‖V^π − V^{π'}‖∞` (`trajectoryExpectedQ_sub_norm_le`).
-/

open MeasureTheory

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual forced-action Q values differ by at most `γ` times the actual state values:
`Q^π(s,a) − Q^{π'}(s,a) = γ ⟨P(·|s,a), V^π − V^{π'}⟩`. -/
theorem trajectoryExpectedQ_sub_norm_le (M : DiscountedMDP State Action)
    (π π' : StationaryPolicy State Action) :
    ‖M.trajectoryExpectedQ π - M.trajectoryExpectedQ π'‖ ≤
      M.discount * ‖M.trajectoryExpectedValue π - M.trajectoryExpectedValue π'‖ := by
  have hB : 0 ≤ M.discount * ‖M.trajectoryExpectedValue π - M.trajectoryExpectedValue π'‖ :=
    mul_nonneg M.discount_nonneg (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hB).2 fun s ↦ (pi_norm_le_iff_of_nonneg hB).2 fun a ↦ ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, M.trajectoryExpectedQ_eq_policyFixedPoint,
    M.policyFixedPoint_eq_reward_add_value, M.policyFixedPoint_eq_reward_add_value,
    ← M.trajectoryExpectedValue_eq_valueFixedPoint, ← M.trajectoryExpectedValue_eq_valueFixedPoint]
  have hrow := (M.transition s a).abs_expectation_sub_le
    (f := M.trajectoryExpectedValue π) (g := M.trajectoryExpectedValue π')
    (c := ‖M.trajectoryExpectedValue π - M.trajectoryExpectedValue π'‖) (fun t ↦ by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (M.trajectoryExpectedValue π - M.trajectoryExpectedValue π') t)
  have heq : M.reward s a + M.discount * (M.transition s a).expectation (M.trajectoryExpectedValue π) -
      (M.reward s a + M.discount * (M.transition s a).expectation (M.trajectoryExpectedValue π')) =
      M.discount * ((M.transition s a).expectation (M.trajectoryExpectedValue π) -
        (M.transition s a).expectation (M.trajectoryExpectedValue π')) := by ring
  rw [heq, abs_mul, abs_of_nonneg M.discount_nonneg]
  exact mul_le_mul_of_nonneg_left hrow M.discount_nonneg

/-- Since `γ < 1`, a Q gap above `ε` forces a value gap above `ε`. -/
theorem lt_value_gap_of_lt_Q_gap (M : DiscountedMDP State Action)
    (π π' : StationaryPolicy State Action) {ε : ℝ}
    (h : ε < ‖M.trajectoryExpectedQ π - M.trajectoryExpectedQ π'‖) :
    ε < ‖M.trajectoryExpectedValue π' - M.trajectoryExpectedValue π‖ := by
  have h1 := M.trajectoryExpectedQ_sub_norm_le π π'
  have h2 : M.discount * ‖M.trajectoryExpectedValue π - M.trajectoryExpectedValue π'‖ ≤
      ‖M.trajectoryExpectedValue π - M.trajectoryExpectedValue π'‖ :=
    mul_le_of_le_one_left (norm_nonneg _) M.discount_lt_one.le
  rw [norm_sub_rev]
  linarith

end StatisticalRL.DiscountedMDP

namespace StatisticalRL.GenerativeLowerBound

open StatisticalRL.ModelBasedPolicyLearning StatisticalRL.DiscountedMDP

/-- Burn-in necessity (restricted reading of `generative_model_model_based.tex:934–940`): with
`N ≤ log(SA)/(8(1−γ))` samples per pair, every deterministic policy estimator has value gap
`‖V⋆ − V^{π̂}‖∞ > 1/(64(1−γ))` with probability at least `1/4` on some MDP with discount `γ`.
Corollary of `theorem37_corrected_fin_carriers` at `ε = 1/(64(1−γ))`. -/
theorem burnIn_necessary_valueGap (S A N : ℕ) (γ : ℝ)
    (hS : 2 ≤ S) (hA : 2 ≤ A) (hSA : 16 ≤ S * A) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hN : (N : ℝ) ≤ Real.log ((S : ℝ) * (A : ℝ)) / (8 * (1 - γ)))
    (piHat : (Fin S → Fin A → ℝ) → ℝ → Samples (Fin S) (Fin A) N → Fin S → Fin A) :
    ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ (samplingLaw M N).real
        {data | 1 / (64 * (1 - γ)) <
          ‖M.trajectoryExpectedValue M.optimalGreedyPolicy -
            M.trajectoryExpectedValue
              (fun s ↦ EnvironmentStage.pointMass (piHat M.reward M.discount data s))‖} := by
  have hg : 0 < 1 - γ := sub_pos.mpr hγ1
  set ε : ℝ := 1 / (64 * (1 - γ)) with hε_def
  have hε : 0 < ε := by positivity
  have hεmax : ε < 1 / (32 * (1 - γ)) := by
    rw [hε_def]
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  have hbudget : (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2) := by
    have hrw : (1 / 32768) * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2) =
        Real.log ((S : ℝ) * (A : ℝ)) / (8 * (1 - γ)) := by
      rw [hε_def]
      field_simp
      ring
    rw [hrw]
    exact hN
  obtain ⟨M, hMγ, hrisk⟩ :=
    (theorem37_corrected_fin_carriers S A N γ ε hS hSA hγ hγ1 hε hεmax hbudget).1 hA piHat
  refine ⟨M, hMγ, hrisk.trans (measureReal_mono ?_)⟩
  intro data hdata
  exact M.lt_value_gap_of_lt_Q_gap _ _ hdata

end StatisticalRL.GenerativeLowerBound
