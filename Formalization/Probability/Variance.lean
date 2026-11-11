import Formalization.MDP.Basic
import Formalization.Probability.VarianceDefinitions

/-!
# Finite transition variance and its perturbation bound

The definition is the actual finite second moment minus squared first moment
from `eq:defn-Var-Psa-V` of arXiv:2610.41903v1. The final theorem proves
`lem:variance-perturbation-var-P-V` for the actual stochastic transition rows,
with the source's constant and supremum norms.
-/

namespace StatisticalRL

/-- Perturbing two bounded scalars controls their squared difference. -/
theorem abs_sq_sub_sq_le {x y B ε : ℝ} (hε : 0 ≤ ε)
    (hx : |x| ≤ B) (hy : |y| ≤ B) (hxy : |x - y| ≤ ε) :
    |x ^ 2 - y ^ 2| ≤ 2 * B * ε := by
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
  calc
    |x - y| * |x + y| ≤ ε * (B + B) :=
      mul_le_mul hxy ((abs_add_le x y).trans (add_le_add hx hy)) (abs_nonneg _) hε
    _ = 2 * B * ε := by ring

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

/-- The second-moment expression equals the expectation of the actual centered square. -/
theorem variance_eq_expectation_centered_sq (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    d.variance f = d.expectation (fun x ↦ (f x - d.expectation f) ^ 2) := by
  have hexpand : (fun x ↦ (f x - d.expectation f) ^ 2) =
      (fun x ↦ f x ^ 2 - (2 * d.expectation f) * f x + (d.expectation f) ^ 2) := by
    funext x
    ring
  rw [hexpand, expectation_add, expectation_sub, expectation_mul, expectation_const]
  unfold variance
  ring

theorem variance_nonneg (d : FiniteDistribution Ω) (f : Ω → ℝ) : 0 ≤ d.variance f := by
  rw [variance_eq_expectation_centered_sq]
  exact d.expectation_nonneg (fun x ↦ sq_nonneg _)

@[simp]
theorem variance_const (d : FiniteDistribution Ω) (c : ℝ) :
    d.variance (fun _ ↦ c) = 0 := by
  simp only [variance, expectation_const, sub_self]

theorem variance_le_expectation_sq (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    d.variance f ≤ d.expectation (fun x ↦ f x ^ 2) :=
  sub_le_self _ (sq_nonneg _)

/-- Uniform finite-probability variance perturbation, before specializing to transition rows. -/
theorem abs_variance_sub_le (d : FiniteDistribution Ω) {f g : Ω → ℝ} {B ε : ℝ}
    (hε : 0 ≤ ε) (hf : ∀ x, |f x| ≤ B) (hg : ∀ x, |g x| ≤ B)
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    |d.variance f - d.variance g| ≤ 4 * B * ε := by
  have hfirst : |d.expectation (fun x ↦ f x ^ 2) -
      d.expectation (fun x ↦ g x ^ 2)| ≤ 2 * B * ε :=
    d.abs_expectation_sub_le (fun x ↦ abs_sq_sub_sq_le hε (hf x) (hg x) (hfg x))
  have hsecond : |(d.expectation f) ^ 2 - (d.expectation g) ^ 2| ≤ 2 * B * ε :=
    abs_sq_sub_sq_le hε (d.abs_expectation_le hf) (d.abs_expectation_le hg)
      (d.abs_expectation_sub_le hfg)
  have hdecompose : d.variance f - d.variance g =
      (d.expectation (fun x ↦ f x ^ 2) - d.expectation (fun x ↦ g x ^ 2)) -
        ((d.expectation f) ^ 2 - (d.expectation g) ^ 2) := by
    unfold variance
    ring
  rw [hdecompose]
  calc
    |(d.expectation (fun x ↦ f x ^ 2) - d.expectation (fun x ↦ g x ^ 2)) -
        ((d.expectation f) ^ 2 - (d.expectation g) ^ 2)| ≤
        |d.expectation (fun x ↦ f x ^ 2) - d.expectation (fun x ↦ g x ^ 2)| +
          |(d.expectation f) ^ 2 - (d.expectation g) ^ 2| := abs_sub _ _
    _ ≤ 2 * B * ε + 2 * B * ε := add_le_add hfirst hsecond
    _ = 4 * B * ε := by ring

end FiniteDistribution

namespace DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The source's `Var_P(V)`, indexed by the actual state-action transition rows. -/
def transitionVariance (M : DiscountedMDP State Action) (V : State → ℝ)
    (s : State) (a : Action) : ℝ :=
  (M.transition s a).variance V

/-- Lemma 2.2: exact transition-variance perturbation bound, with the original constant. -/
theorem transitionVariance_perturbation (M : DiscountedMDP State Action)
    {V Vhat : State → ℝ}
    (hV : ∀ s, 0 ≤ V s ∧ V s ≤ 1 / (1 - M.discount))
    (hVhat : ∀ s, 0 ≤ Vhat s ∧ Vhat s ≤ 1 / (1 - M.discount)) :
    ‖M.transitionVariance Vhat - M.transitionVariance V‖ ≤
      (4 / (1 - M.discount)) * ‖Vhat - V‖ := by
  have hc : 0 ≤ (4 / (1 - M.discount)) * ‖Vhat - V‖ :=
    mul_nonneg (div_nonneg (by norm_num) (sub_pos.mpr M.discount_lt_one).le) (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro a
  rw [Real.norm_eq_abs]
  have hf (t : State) : |Vhat t| ≤ 1 / (1 - M.discount) := by
    rw [abs_of_nonneg (hVhat t).1]
    exact (hVhat t).2
  have hg (t : State) : |V t| ≤ 1 / (1 - M.discount) := by
    rw [abs_of_nonneg (hV t).1]
    exact (hV t).2
  have hfg (t : State) : |Vhat t - V t| ≤ ‖Vhat - V‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (Vhat - V) t
  have hrow := (M.transition s a).abs_variance_sub_le (norm_nonneg _) hf hg hfg
  simpa only [transitionVariance, Pi.sub_apply, div_eq_mul_inv, one_mul, mul_assoc] using hrow

end DiscountedMDP

end StatisticalRL
