import Formalization.Probability.Variance
import Mathlib.Data.Real.Sqrt

/-! Standard-deviation stability and the deterministic leave-one-out Bernstein
radius transfer. No concentration event or independence theorem is asserted. -/
open scoped BigOperators
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]

/-- Cauchy-Schwarz for the actual finite probability expectation. -/
theorem expectation_mul_le_sqrt_secondMoments (d : FiniteDistribution State) (f g : State → ℝ) :
    d.expectation (fun s ↦ f s * g s) ≤
      Real.sqrt (d.expectation (fun s ↦ f s ^ 2)) *
        Real.sqrt (d.expectation (fun s ↦ g s ^ 2)) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun s ↦ Real.sqrt (d.prob s) * f s) (fun s ↦ Real.sqrt (d.prob s) * g s)
  have hprod (s : State) : (Real.sqrt (d.prob s) * f s) * (Real.sqrt (d.prob s) * g s) =
      d.prob s * (f s * g s) := by
    calc
      _ = (Real.sqrt (d.prob s)) ^ 2 * (f s * g s) := by ring
      _ = _ := by rw [Real.sq_sqrt (d.prob_nonneg s)]
  have hsq (v : State → ℝ) (s : State) : (Real.sqrt (d.prob s) * v s) ^ 2 =
      d.prob s * v s ^ 2 := by rw [mul_pow, Real.sq_sqrt (d.prob_nonneg s)]
  simp only [hprod, hsq] at h
  exact h

/-- Minkowski's inequality for square roots of finite second moments. -/
theorem sqrt_secondMoment_add_le (d : FiniteDistribution State) (f g : State → ℝ) :
    Real.sqrt (d.expectation (fun s ↦ (f s + g s) ^ 2)) ≤
      Real.sqrt (d.expectation (fun s ↦ f s ^ 2)) +
        Real.sqrt (d.expectation (fun s ↦ g s ^ 2)) := by
  have hcross := expectation_mul_le_sqrt_secondMoments d f g
  have hf : 0 ≤ d.expectation (fun s ↦ f s ^ 2) := d.expectation_nonneg (fun _ ↦ sq_nonneg _)
  have hg : 0 ≤ d.expectation (fun s ↦ g s ^ 2) := d.expectation_nonneg (fun _ ↦ sq_nonneg _)
  have heq : d.expectation (fun s ↦ (f s + g s) ^ 2) =
      d.expectation (fun s ↦ f s ^ 2) + 2 * d.expectation (fun s ↦ f s * g s) +
        d.expectation (fun s ↦ g s ^ 2) := by
    have hfun : (fun s ↦ (f s + g s) ^ 2) =
        (fun s ↦ (f s ^ 2 + 2 * (f s * g s)) + g s ^ 2) := by funext s; ring
    rw [hfun, expectation_add, expectation_add, expectation_mul]
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  rw [heq]
  nlinarith only [hcross, Real.sq_sqrt hf, Real.sq_sqrt hg]

/-- Standard deviation is subadditive for arbitrary real state vectors. -/
theorem sqrt_variance_add_le (d : FiniteDistribution State) (f g : State → ℝ) :
    Real.sqrt (d.variance (fun s ↦ f s + g s)) ≤
      Real.sqrt (d.variance f) + Real.sqrt (d.variance g) := by
  rw [variance_eq_expectation_centered_sq, variance_eq_expectation_centered_sq,
    variance_eq_expectation_centered_sq]
  have heq : (fun s ↦ (f s + g s - d.expectation (fun t ↦ f t + g t)) ^ 2) =
      (fun s ↦ ((f s - d.expectation f) + (g s - d.expectation g)) ^ 2) := by
    rw [expectation_add]
    funext s
    ring
  rw [heq]
  exact sqrt_secondMoment_add_le d _ _

/-- A finite row's standard deviation never exceeds the vector's sup norm. -/
theorem sqrt_variance_le_norm (d : FiniteDistribution State) (f : State → ℝ) :
    Real.sqrt (d.variance f) ≤ ‖f‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg _, (d.variance_le_expectation_sq f).trans ?_⟩
  apply d.expectation_le_const
  intro s
  have hs : |f s| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm f s
  nlinarith [sq_abs (f s), abs_nonneg (f s), norm_nonneg f]

/-- Source standard-deviation triangle inequality with a uniform perturbation. -/
theorem sqrt_variance_le_add_norm_sub (d : FiniteDistribution State) (f g : State → ℝ) :
    Real.sqrt (d.variance g) ≤ Real.sqrt (d.variance f) + ‖g - f‖ := by
  have h := sqrt_variance_add_le d f (fun s ↦ g s - f s)
  have heq : (fun s ↦ f s + (g s - f s)) = g := by funext s; ring
  rw [heq] at h
  exact h.trans (add_le_add le_rfl (sqrt_variance_le_norm d (g - f)))

/-- Standard deviation is 1-Lipschitz in the finite sup norm, including zero variance. -/
theorem abs_sqrt_variance_sub_le_norm (d : FiniteDistribution State) (f g : State → ℝ) :
    |Real.sqrt (d.variance f) - Real.sqrt (d.variance g)| ≤ ‖f - g‖ := by
  have hfg := sqrt_variance_le_add_norm_sub d g f
  have hgf := sqrt_variance_le_add_norm_sub d f g
  rw [norm_sub_rev g f] at hgf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exact source implication from a proved covering distance. -/
theorem sqrt_variance_le_of_norm_sub_le (d : FiniteDistribution State) (f g : State → ℝ)
    (ε : ℝ) (hcover : ‖f - g‖ ≤ ε) :
    Real.sqrt (d.variance g) ≤ Real.sqrt (d.variance f) + ε := by
  have h := (abs_le.mp (abs_sqrt_variance_sub_le_norm d f g)).1
  linarith

/-- Changing the value vector changes a difference of probability-row means
by at most twice its sup-norm perturbation. -/
theorem residual_sub_le_two_norm (p q : FiniteDistribution State) (f g : State → ℝ) :
    |(q.expectation f - p.expectation f) - (q.expectation g - p.expectation g)| ≤ 2 * ‖f - g‖ := by
  have hp := p.abs_expectation_sub_le (f := f) (g := g)
    (fun s ↦ by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (f - g) s)
  have hq := q.abs_expectation_sub_le (f := f) (g := g)
    (fun s ↦ by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (f - g) s)
  have heq : (q.expectation f - p.expectation f) - (q.expectation g - p.expectation g) =
      (q.expectation f - q.expectation g) - (p.expectation f - p.expectation g) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

/-- Deterministic fixed-grid Bernstein-radius transfer, before source constants
are simplified. The close vector's concentration estimate is consumed explicitly. -/
theorem bernstein_radius_transfer (p q : FiniteDistribution State) (f g : State → ℝ)
    (ε a b : ℝ) (ha : 0 ≤ a) (hcover : ‖f - g‖ ≤ ε)
    (hgrid : |q.expectation g - p.expectation g| ≤ a * Real.sqrt (p.variance g) + b) :
    |q.expectation f - p.expectation f| ≤
      a * Real.sqrt (p.variance f) + (2 + a) * ε + b := by
  have hr := (residual_sub_le_two_norm p q f g).trans
    (mul_le_mul_of_nonneg_left hcover (by norm_num : (0 : ℝ) ≤ 2))
  have hs := mul_le_mul_of_nonneg_left (sqrt_variance_le_of_norm_sub_le p f g ε hcover) ha
  have ht : |q.expectation f - p.expectation f| ≤
      |q.expectation g - p.expectation g| +
        |(q.expectation f - p.expectation f) - (q.expectation g - p.expectation g)| := by
    convert abs_add_le (q.expectation g - p.expectation g)
      ((q.expectation f - p.expectation f) - (q.expectation g - p.expectation g)) using 1; congr 1; ring
  nlinarith only [ht, hgrid, hr, hs]

/-- The source's last radius simplification with ε=1/(Nh), β≥4 and N≥1. -/
theorem source_cover_radius_arithmetic (N : ℕ) (hN : 0 < N) (h β : ℝ)
    (hh : 0 < h) (hβ : 4 ≤ β) :
    (2 + Real.sqrt (β / N)) * (1 / ((N : ℝ) * h)) + β / (3 * N * h) ≤
      2 * β / ((N : ℝ) * h) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb0 : 0 ≤ β := by linarith
  have ht : β / N ≤ β := (div_le_iff₀ hn).2 (by nlinarith)
  have hroot : Real.sqrt (β / N) ≤ β / 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    have hp := mul_nonneg hb0 (sub_nonneg.mpr hβ)
    nlinarith
  have hnum : 2 + Real.sqrt (β / N) + β / 3 ≤ 2 * β := by linarith
  calc
    _ = (2 + Real.sqrt (β / N) + β / 3) / ((N : ℝ) * h) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hn hh).le

/-- Source-ready row transfer with the exact coefficient 2β/(Nh). -/
theorem bernstein_radius_transfer_source (p q : FiniteDistribution State)
    (f g : State → ℝ) (N : ℕ) (hN : 0 < N) (h β : ℝ) (hh : 0 < h) (hβ : 4 ≤ β)
    (hcover : ‖f - g‖ ≤ 1 / ((N : ℝ) * h))
    (hgrid : |q.expectation g - p.expectation g| ≤
      Real.sqrt (β / N) * Real.sqrt (p.variance g) + β / (3 * N * h)) :
    |q.expectation f - p.expectation f| ≤
      Real.sqrt (β / N) * Real.sqrt (p.variance f) + 2 * β / ((N : ℝ) * h) := by
  have ht := bernstein_radius_transfer p q f g (1 / ((N : ℝ) * h))
    (Real.sqrt (β / N)) (β / (3 * N * h)) (Real.sqrt_nonneg _) hcover hgrid
  have ha := source_cover_radius_arithmetic N hN h β hh hβ
  linarith

end StatisticalRL.FiniteDistribution
