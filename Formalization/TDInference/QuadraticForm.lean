import Formalization.TDInference.LinearisedCovariance

/-!
# Theorem 7.11 support (M8): the covariance error in a fixed direction

Source: `chapters/inference.tex:104–117` (`Λ⋆ = A⁻¹ΓA⁻ᵀ`, `Γ := Γ_true`, SOURCE-ISSUES C43), :134.
Library infrastructure only; no source result is claimed.

`abs_quadForm_linCov_sub_le`: for every direction `u`,
`|uᵀ(Λ_T − A⁻¹ diag(Γ_true) A⁻ᵀ)u| ≤ ‖u‖₁² K_Λ T^{-1/3}`, the quadratic-form corollary of the
entrywise B5 bound `abs_linCov_sub_le` (CRITIC-M5 note F2), under the same hypotheses
(`0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`; no `Γ ≻ 0`).
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- An entrywise bound `|X(s,s')| ≤ c` gives `|uᵀXu| ≤ ‖u‖₁² c`. -/
theorem abs_quadForm_le_of_abs_apply_le {n : Type*} [Fintype n] (X : Matrix n n ℝ)
    (u : n → ℝ) {c : ℝ} (h : ∀ s s', |X s s'| ≤ c) :
    |∑ s, ∑ s', u s * u s' * X s s'| ≤ (∑ s, |u s|) ^ 2 * c := by
  calc |∑ s, ∑ s', u s * u s' * X s s'|
      ≤ ∑ s, ∑ s', |u s| * |u s'| * c := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦ ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s' _ ↦ ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (h s s') (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ s, |u s|) ^ 2 * c := by
        rw [sq, sum_mul_sum, sum_mul]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [sum_mul]

/-- **Quadratic-form covariance error.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)` for all `s`,
`T ≥ 1` and every `u : State → ℝ`,
`|∑_{s,s'} u(s)u(s')(Λ_T − A⁻¹ diag(Γ_true) A⁻ᵀ)(s,s')| ≤ (∑_s |u(s)|)² K_Λ T^{-1/3}`
with the `T`-free `K_Λ = linCovConst`. -/
theorem abs_quadForm_linCov_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (hT : 1 ≤ T) (u : State → ℝ) :
    |∑ s, ∑ s', u s * u s' * (linCov M π μ η₀ T s s' -
        ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ) s s')| ≤
      (∑ s, |u s|) ^ 2 * linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  rw [mul_assoc ((∑ s, |u s|) ^ 2)]
  exact abs_quadForm_le_of_abs_apply_le
    (linCov M π μ η₀ T - (tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ) u
    fun s s' ↦ abs_linCov_sub_le M π μ h0 h1 hμmin0 hμmin hT s s'

end StatisticalRL.Ch7Rest.TDInference
