import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Corrected Theorem 7.12: scalar inequalities

Elementary real inequalities used in the online VPO regret proof (steps
L6, L7, log-sigmoid Lipschitz, exponential bounds).
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

/-- Jensen for the square: for weights `c ≥ 0` with `∑ c = 1`, `(∑ c a)² ≤ ∑ c a²`. -/
theorem sq_wsum_le {ι : Type*} (s : Finset ι) (c a : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (h1 : ∑ i ∈ s, c i = 1) : (∑ i ∈ s, c i * a i) ^ 2 ≤ ∑ i ∈ s, c i * a i ^ 2 := by
  set m := ∑ i ∈ s, c i * a i
  have h0 : 0 ≤ ∑ i ∈ s, c i * (a i - m) ^ 2 :=
    sum_nonneg fun i hi ↦ mul_nonneg (hc i hi) (sq_nonneg _)
  have hexp : ∑ i ∈ s, c i * (a i - m) ^ 2 =
      ∑ i ∈ s, c i * a i ^ 2 - 2 * m * m + m ^ 2 * ∑ i ∈ s, c i := by
    have hi : ∀ i, c i * (a i - m) ^ 2 = c i * a i ^ 2 - 2 * m * (c i * a i) + m ^ 2 * c i := by
      intro i; ring
    rw [sum_congr rfl fun i _ ↦ hi i, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [hexp, h1] at h0
  nlinarith

/-- Bernoulli Hellinger bound (L6): for `p, q ∈ [0,1]`,
`(p − q)² ≤ 2 (1 − (√p √q + √(1−p) √(1−q)))`. -/
theorem sq_sub_le_two_hellinger {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (p - q) ^ 2 ≤ 2 * (1 - (√p * √q + √(1 - p) * √(1 - q))) := by
  set s := √p
  set t := √q
  set u := √(1 - p)
  set v := √(1 - q)
  have hs : s ^ 2 = p := sq_sqrt hp0
  have ht : t ^ 2 = q := sq_sqrt hq0
  have hu : u ^ 2 = 1 - p := sq_sqrt (by linarith)
  have hv : v ^ 2 = 1 - q := sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have ht0 : 0 ≤ t := sqrt_nonneg _
  have hu0 : 0 ≤ u := sqrt_nonneg _
  have hv0 : 0 ≤ v := sqrt_nonneg _
  have hsu : s ^ 2 + u ^ 2 = 1 := by rw [hs, hu]; ring
  have htv : t ^ 2 + v ^ 2 = 1 := by rw [ht, hv]; ring
  -- Lagrange identities
  have hL1 : (s * v + t * u) ^ 2 + (s * t - u * v) ^ 2 = (s ^ 2 + u ^ 2) * (t ^ 2 + v ^ 2) := by
    ring
  have hL2 : (s * t + u * v) ^ 2 + (s * v - t * u) ^ 2 = (s ^ 2 + u ^ 2) * (t ^ 2 + v ^ 2) := by
    ring
  have hpq : p - q = (s * v - t * u) * (s * v + t * u) := by
    rw [← hs, ← ht]
    have : s ^ 2 - t ^ 2 = s ^ 2 * (t ^ 2 + v ^ 2) - t ^ 2 * (s ^ 2 + u ^ 2) := by
      rw [hsu, htv]; ring
    rw [this]; ring
  have hplus : (s * v + t * u) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (s * t - u * v)]
  have hBC : (s * t + u * v) ^ 2 + (s * v - t * u) ^ 2 = 1 := by rw [hL2, hsu, htv]; ring
  have hBC0 : 0 ≤ s * t + u * v := by positivity
  have hBC1 : s * t + u * v ≤ 1 := by nlinarith [sq_nonneg (s * v - t * u)]
  have h1 : (p - q) ^ 2 ≤ (s * v - t * u) ^ 2 := by
    rw [hpq, mul_pow]
    calc (s * v - t * u) ^ 2 * (s * v + t * u) ^ 2 ≤ (s * v - t * u) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hplus (sq_nonneg _)
      _ = _ := mul_one _
  nlinarith

/-- Lower bound on the sigmoid derivative: for `|x| ≤ a`, `σ(x)(1 − σ(x)) ≥ 1/(4e^a)`. -/
theorem sigmoid_deriv_lower {a x : ℝ} (ha : 0 ≤ a) (hx : |x| ≤ a) :
    1 / (4 * exp a) ≤ sigmoid x * (1 - sigmoid x) := by
  have hσ : sigmoid x * (1 - sigmoid x) = exp (-x) / (1 + exp (-x)) ^ 2 := by
    rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg x, sigmoid_def]
    field_simp
  rw [hσ]
  set w := exp (-x) with hw
  set E := exp a with hE
  have hw0 : 0 < w := exp_pos _
  have hE1 : 1 ≤ E := one_le_exp ha
  have hwE : w ≤ E := exp_le_exp.2 (by linarith [neg_abs_le x, le_abs_self x, neg_le_abs x])
  have hEw : E⁻¹ ≤ w := by
    rw [hw, hE, ← exp_neg]; exact exp_le_exp.2 (by linarith [le_abs_self x])
  have hEinv : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE1
  have hEE : E * E⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hq : w ^ 2 + 1 ≤ (E + E⁻¹) * w := by nlinarith [mul_nonneg (sub_nonneg.2 hEw) (sub_nonneg.2 hwE)]
  have hkey : (1 + w) ^ 2 ≤ 4 * E * w := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Inverse Lipschitz bound for the sigmoid (L7): for `|a|, |b| ≤ c`,
`(a − b)² ≤ 16 e^{2c} (σ a − σ b)²`. -/
theorem sq_sub_le_sigmoid {c a b : ℝ} (hc : 0 ≤ c) (ha : |a| ≤ c) (hb : |b| ≤ c) :
    (a - b) ^ 2 ≤ 16 * exp (2 * c) * (sigmoid a - sigmoid b) ^ 2 := by
  -- `|σ a − σ b| ≥ |a − b| / (4 e^c)`
  have key : ∀ a b : ℝ, |a| ≤ c → |b| ≤ c → a < b → (b - a) / (4 * exp c) ≤ sigmoid b - sigmoid a := by
    intro a b ha hb hab
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope sigmoid
      (fun x ↦ sigmoid x * (1 - sigmoid x)) hab continuous_sigmoid.continuousOn
      (fun x _ ↦ hasDerivAt_sigmoid x)
    have hξc : |ξ| ≤ c := by
      rw [abs_le] at ha hb ⊢
      exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
    have hlow := sigmoid_deriv_lower hc hξc
    rw [hξeq] at hlow
    have hba : 0 < b - a := by linarith
    rw [le_div_iff₀ hba] at hlow
    calc (b - a) / (4 * exp c) = 1 / (4 * exp c) * (b - a) := by ring
      _ ≤ _ := hlow
  have hE : exp (2 * c) = exp c ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hc0 : 0 < exp c := exp_pos c
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h := key a b ha hb hab
    have h0 : 0 ≤ (b - a) / (4 * exp c) := div_nonneg (by linarith) (by positivity)
    have h2 := pow_le_pow_left₀ h0 h 2
    rw [div_pow] at h2
    rw [hE]
    have : (a - b) ^ 2 = (b - a) ^ 2 := by ring
    rw [this, div_le_iff₀ (by positivity)] at *
    nlinarith [sq_nonneg (sigmoid b - sigmoid a)]
  · simp
  · have h := key b a hb ha hab
    have h0 : 0 ≤ (a - b) / (4 * exp c) := div_nonneg (by linarith) (by positivity)
    have h2 := pow_le_pow_left₀ h0 h 2
    rw [div_pow, div_le_iff₀ (by positivity)] at h2
    rw [hE]
    nlinarith [sq_nonneg (sigmoid a - sigmoid b)]

/-- `log σ` is 1-Lipschitz. -/
theorem abs_log_sigmoid_sub_le (a b : ℝ) : |log (sigmoid a) - log (sigmoid b)| ≤ |a - b| := by
  -- `σ b ≤ e^{b-a} σ a` for `a ≤ b`
  have key : ∀ a b : ℝ, a ≤ b → log (sigmoid b) - log (sigmoid a) ≤ b - a ∧
      0 ≤ log (sigmoid b) - log (sigmoid a) := by
    intro a b hab
    have hsa := sigmoid_pos a
    have hsb := sigmoid_pos b
    refine ⟨?_, sub_nonneg.2 (log_le_log hsa (sigmoid_le hab))⟩
    have hle : sigmoid b ≤ exp (b - a) * sigmoid a := by
      rw [sigmoid_def, sigmoid_def, ← div_eq_mul_inv, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have h1 : 1 ≤ exp (b - a) := one_le_exp (by linarith)
      have h2 : exp (b - a) * exp (-b) = exp (-a) := by rw [← exp_add]; ring_nf
      nlinarith [exp_pos (-b)]
    have := log_le_log hsb hle
    rw [log_mul (exp_pos _).ne' hsa.ne', log_exp] at this
    linarith
  rcases le_total a b with hab | hab
  · obtain ⟨h1, h2⟩ := key a b hab
    rw [abs_sub_comm, abs_of_nonneg h2, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · obtain ⟨h1, h2⟩ := key b a hab
    rw [abs_of_nonneg h2, abs_of_nonneg (by linarith)]
    exact h1

/-- `e^x ≤ 1 + x + (x²/2) e^{|x|}`. -/
theorem exp_le_quadratic (x : ℝ) : exp x ≤ 1 + x + x ^ 2 / 2 * exp |x| := by
  rcases le_total 0 x with hx | hx
  · -- `h(y) = (1+y) e^{-y} + y²/2` is monotone
    have hmono : Monotone (fun y : ℝ ↦ (1 + y) * exp (-y) + y ^ 2 / 2) := by
      refine monotone_of_hasDerivAt_nonneg (f' := fun y ↦ y * (1 - exp (-y))) (fun y ↦ ?_)
        (fun y ↦ ?_)
      · have h1 : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 y := (hasDerivAt_id y).const_add 1
        have h2 : HasDerivAt (fun y : ℝ ↦ exp (-y)) (exp (-y) * (-1)) y :=
          (hasDerivAt_neg y).exp
        have h3 : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) (↑2 * y ^ (2 - 1) / 2) y :=
          (hasDerivAt_pow 2 y).div_const 2
        convert (h1.mul h2).add h3 using 1
        simp; try ring
      · show 0 ≤ y * (1 - exp (-y))
        rcases le_total 0 y with hy | hy
        · exact mul_nonneg hy (sub_nonneg.2 (exp_le_one_iff.2 (by linarith)))
        · exact mul_nonneg_of_nonpos_of_nonpos hy (sub_nonpos.2 (one_le_exp (by linarith)))
    have h := hmono hx
    simp only [neg_zero, exp_zero, add_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div] at h
    rw [abs_of_nonneg hx]
    have hex : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have hx0 : 0 < exp x := exp_pos x
    nlinarith [mul_le_mul_of_nonneg_left h hx0.le]
  · -- `k(y) = 1 + y + y²/2 − e^y` is antitone
    have hanti : Antitone (fun y : ℝ ↦ 1 + y + y ^ 2 / 2 - exp y) := by
      refine antitone_of_hasDerivAt_nonpos (f' := fun y ↦ 1 + y - exp y) (fun y ↦ ?_)
        (fun y ↦ ?_)
      · have h3 : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) (↑2 * y ^ (2 - 1) / 2) y :=
          (hasDerivAt_pow 2 y).div_const 2
        convert (((hasDerivAt_id y).const_add 1).add h3).sub (hasDerivAt_exp y) using 1
        simp; try ring
      · show 1 + y - exp y ≤ 0
        linarith [add_one_le_exp y]
    have h := hanti hx
    simp only [add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      exp_zero, sub_self] at h
    have h1 : 1 ≤ exp |x| := one_le_exp (abs_nonneg x)
    nlinarith [sq_nonneg x]

/-- Convexity bound: for `x ∈ [0,1]`, `e^{-x} ≤ 1 − (1 − e^{-1}) x`. -/
theorem exp_neg_le_affine {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp (-x) ≤ 1 - (1 - exp (-1)) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (sub_nonneg.2 hx1) hx0 (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one, mul_neg] at h
  linarith

/-- Per-term Gibbs inequality: for `p ≥ 0` and `q > 0`, `p − q ≤ p log(p/q)`. -/
theorem sub_le_mul_log_div {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : p - q ≤ p * log (p / q) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp; exact hq.le
  · have h := log_le_sub_one_of_pos (div_pos hq hp)
    rw [log_div hq.ne' hp.ne'] at h
    rw [log_div hp.ne' hq.ne']
    have : q / p * p = q := div_mul_cancel₀ q hp.ne'
    nlinarith

/-- For `x ∈ [0,1]`, `x ≤ 2 log(1 + x)`. -/
theorem le_two_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ 2 * log (1 + x) := by
  have h := one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + x)
  have h2 : x / 2 ≤ 1 - (1 + x)⁻¹ := by
    rw [inv_eq_one_div, le_sub_iff_add_le, div_add_div _ _ (by norm_num) (by linarith),
      div_le_one (by positivity)]
    nlinarith
  linarith

end StatisticalRL.Ch7Rest.Rlhf
