import Formalization.RobustRL.DRVI.ResidualVariance
import Formalization.Generative.PolicyLearningVarianceTransfer

/-!
# Deterministic variance tools for the robust deviation bounds (milestone 3, plan §3.4)

* `variance_le_sq_dev`: `Var_p f ≤ E_p (f − c)^2`.
* `variance_min_le`: clipping contracts the variance, `Var_p(min(f,α)) ≤ Var_p f`.
* `variance_centeredSq_le`: `Var_p((f − E_p f)^2) ≤ B^2 Var_p f` for `0 ≤ f ≤ B`.
* `std_deviation_le` ((S)): two Bernstein-type hypotheses give
  `|std_{p'} f − std_p f| ≤ 8 B √(ℓ/N)` when `ℓ ≤ N` (the plan states 4; any absolute
  constant suffices and the final constants are re-derived with 8).
* Variance transfer to an admissible row: TV `Var_p f ≤ Var_q f + σ S^2`,
  χ² `Var_p f ≤ Var_q f + (√σ/2) S^2`, where `S` bounds the span of `f`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State : Type*} [Fintype State]

theorem expectation_sq_dev (d : FiniteDistribution State) (f : State → ℝ) (c : ℝ) :
    d.expectation (fun x ↦ (f x - c) ^ 2) = d.variance f + (d.expectation f - c) ^ 2 := by
  have h : (fun x ↦ (f x - c) ^ 2) = fun x ↦ (f x ^ 2 + (-2 * c) * f x) + c ^ 2 := by
    funext x; ring
  rw [h, d.expectation_add, d.expectation_add, d.expectation_mul, d.expectation_const]
  unfold FiniteDistribution.variance
  ring

theorem variance_le_sq_dev (d : FiniteDistribution State) (f : State → ℝ) (c : ℝ) :
    d.variance f ≤ d.expectation (fun x ↦ (f x - c) ^ 2) := by
  rw [expectation_sq_dev]
  nlinarith [sq_nonneg (d.expectation f - c)]

/-- Pairwise form `2 Var_p g = Σ_x Σ_y p_x p_y (g x − g y)^2`. -/
theorem two_variance_eq_pairwise (d : FiniteDistribution State) (g : State → ℝ) :
    2 * d.variance g = ∑ x, ∑ y, d.prob x * d.prob y * (g x - g y) ^ 2 := by
  have hexp : ∀ x y, d.prob x * d.prob y * (g x - g y) ^ 2 =
      d.prob y * (d.prob x * g x ^ 2) + d.prob x * (d.prob y * g y ^ 2) -
        2 * (d.prob x * g x) * (d.prob y * g y) := by intro x y; ring
  simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ x, ∑ y, d.prob y * (d.prob x * g x ^ 2) = d.expectation (fun x ↦ g x ^ 2) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [d.sum_prob, one_mul]; rfl
  have h2 : ∑ x, ∑ y, d.prob x * (d.prob y * g y ^ 2) = d.expectation (fun x ↦ g x ^ 2) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [d.sum_prob, one_mul]; rfl
  have h3 : ∑ x, ∑ y, 2 * (d.prob x * g x) * (d.prob y * g y) = 2 * d.expectation g ^ 2 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    unfold FiniteDistribution.expectation
    rw [← Finset.mul_sum]
    ring
  rw [h1, h2, h3]
  unfold FiniteDistribution.variance
  ring

/-- Any 1-Lipschitz image contracts the variance. -/
theorem variance_comp_le (d : FiniteDistribution State) (f g : State → ℝ)
    (h : ∀ x y, |g x - g y| ≤ |f x - f y|) : d.variance g ≤ d.variance f := by
  have hg := two_variance_eq_pairwise d g
  have hf := two_variance_eq_pairwise d f
  have : ∑ x, ∑ y, d.prob x * d.prob y * (g x - g y) ^ 2 ≤
      ∑ x, ∑ y, d.prob x * d.prob y * (f x - f y) ^ 2 := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (d.prob_nonneg x) (d.prob_nonneg y))
    have := h x y
    have h0 := abs_nonneg (g x - g y)
    nlinarith [sq_abs (g x - g y), sq_abs (f x - f y)]
  linarith

theorem abs_min_sub_min_le (a b α : ℝ) : |min a α - min b α| ≤ |a - b| := by
  rcases le_total a α with ha | ha <;> rcases le_total b α with hb | hb
  · rw [min_eq_left ha, min_eq_left hb]
  · rw [min_eq_left ha, min_eq_right hb]
    rw [abs_le]; constructor
    · cases abs_cases (a - b) <;> linarith
    · cases abs_cases (a - b) <;> linarith
  · rw [min_eq_right ha, min_eq_left hb]
    rw [abs_le]; constructor
    · cases abs_cases (a - b) <;> linarith
    · cases abs_cases (a - b) <;> linarith
  · rw [min_eq_right ha, min_eq_right hb]; simp

/-- Clipping contracts the variance. -/
theorem variance_min_le (d : FiniteDistribution State) (f : State → ℝ) (α : ℝ) :
    d.variance (fun x ↦ min (f x) α) ≤ d.variance f :=
  variance_comp_le d f _ (fun x y ↦ abs_min_sub_min_le (f x) (f y) α)

theorem expectation_mem_Icc (d : FiniteDistribution State) {f : State → ℝ} {lo hi : ℝ}
    (hlo : ∀ x, lo ≤ f x) (hhi : ∀ x, f x ≤ hi) :
    lo ≤ d.expectation f ∧ d.expectation f ≤ hi := by
  constructor
  · have := d.expectation_mono (f := fun _ ↦ lo) hlo
    simpa using this
  · exact d.expectation_le_const hhi

/-- `Var_p((f − E_p f)^2) ≤ B^2 Var_p f` for `0 ≤ f ≤ B`. -/
theorem variance_centeredSq_le (d : FiniteDistribution State) {f : State → ℝ} {B : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    d.variance (fun x ↦ (f x - d.expectation f) ^ 2) ≤ B ^ 2 * d.variance f := by
  set m := d.expectation f
  have hm := expectation_mem_Icc d hf0 hfB
  have hdev : ∀ x, (f x - m) ^ 2 ≤ B ^ 2 := by
    intro x
    have h1 := hf0 x; have h2 := hfB x
    nlinarith [hm.1, hm.2]
  calc d.variance (fun x ↦ (f x - m) ^ 2)
      ≤ d.expectation (fun x ↦ ((f x - m) ^ 2) ^ 2) :=
        FiniteDistribution.variance_le_expectation_sq d _
    _ ≤ d.expectation (fun x ↦ B ^ 2 * (f x - m) ^ 2) := by
        apply d.expectation_mono
        intro x
        have := hdev x
        have h0 : 0 ≤ (f x - m) ^ 2 := sq_nonneg _
        nlinarith
    _ = B ^ 2 * d.variance f := by
        rw [d.expectation_mul, FiniteDistribution.variance_eq_expectation_centered_sq]

theorem variance_le_sq_of_bounds (d : FiniteDistribution State) {f : State → ℝ} {B : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) : d.variance f ≤ B ^ 2 := by
  calc d.variance f ≤ d.expectation (fun x ↦ f x ^ 2) := FiniteDistribution.variance_le_expectation_sq d f
    _ ≤ B ^ 2 := d.expectation_le_const (fun x ↦ by have := hf0 x; have := hfB x; nlinarith)

/-! ## Square-root inequalities -/

theorem abs_sqrt_sub_sqrt_le_sqrt_abs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have hsb := Real.sqrt_le_sqrt hab
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  have h1 : Real.sqrt a ≤ Real.sqrt b + Real.sqrt (a - b) := by
    rw [Real.sqrt_le_left]
    · nlinarith [Real.sq_sqrt hb, Real.sq_sqrt (show 0 ≤ a - b by linarith),
        Real.sqrt_nonneg b, Real.sqrt_nonneg (a - b),
        mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg (a - b))]
    · positivity
  linarith

theorem abs_sqrt_sub_sqrt_le_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / Real.sqrt b := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsa := Real.sqrt_nonneg a
  rw [le_div_iff₀ hsb]
  have hfac : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le]
  have : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← hfac, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt a + Real.sqrt b)]
  have h0 := abs_nonneg (Real.sqrt a - Real.sqrt b)
  nlinarith

/-- Scalar core of (S). -/
theorem std_core {a b B t m : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hB : 0 ≤ B) (hbB : b ≤ B ^ 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hmean : |m| ≤ Real.sqrt 2 * Real.sqrt b * t + 2 / 3 * B * t ^ 2)
    (hsq : |a + m ^ 2 - b| ≤ Real.sqrt 2 * B * Real.sqrt b * t + 2 / 3 * B ^ 2 * t ^ 2) :
    |Real.sqrt a - Real.sqrt b| ≤ 8 * B * t := by
  have hsb0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  have hsbB : Real.sqrt b ≤ B := by
    calc Real.sqrt b ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hbB
      _ = B := Real.sqrt_sq hB
  have hr20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2le : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have hkey : |a - b| ≤ 6 * B * Real.sqrt b * t + 2 * B ^ 2 * t ^ 2 := by
    generalize Real.sqrt b = sb at *
    generalize Real.sqrt 2 = r2 at *
    have ht2t : t ^ 2 ≤ t := by
      calc t ^ 2 = t * t := sq t
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left ht1 ht0
        _ = t := mul_one t
    have ht21 : t ^ 2 ≤ 1 := ht2t.trans ht1
    have hm2 : m ^ 2 ≤ (r2 * sb * t + (2 / 3) * B * t ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg m) hmean 2
    have h1 : |a - b| ≤ |a + m ^ 2 - b| + m ^ 2 := by
      have hab : a - b = (a + m ^ 2 - b) - m ^ 2 := by ring
      rw [hab]; calc |a + m ^ 2 - b - m ^ 2| ≤ |a + m ^ 2 - b| + |m ^ 2| := abs_sub _ _
        _ = |a + m ^ 2 - b| + m ^ 2 := by rw [abs_of_nonneg (sq_nonneg m)]
    have hexp : (r2 * sb * t + (2 / 3) * B * t ^ 2) ^ 2 =
        2 * sb ^ 2 * t ^ 2 + (4 / 3) * r2 * sb * B * t ^ 3 + (4 / 9) * B ^ 2 * t ^ 4 := by
      rw [show (r2 * sb * t + (2 / 3) * B * t ^ 2) ^ 2 = r2 ^ 2 * sb ^ 2 * t ^ 2 +
        (4 / 3) * r2 * sb * B * t ^ 3 + (4 / 9) * B ^ 2 * t ^ 4 by ring, hr22]
    have e1 : 2 * sb ^ 2 * t ^ 2 ≤ 2 * B * sb * t := by
      have h1' : sb * t ^ 2 ≤ B * t := mul_le_mul hsbB ht2t (sq_nonneg t) hB
      have := mul_le_mul_of_nonneg_left h1' hsb0
      have e : 2 * sb ^ 2 * t ^ 2 = 2 * (sb * (sb * t ^ 2)) := by ring
      have e' : 2 * B * sb * t = 2 * (sb * (B * t)) := by ring
      rw [e, e']; linarith
    have e2 : (4 / 3) * r2 * sb * B * t ^ 3 ≤ 2 * B * sb * t := by
      have h3 : t ^ 3 ≤ t := by
        have : t ^ 3 = t * t ^ 2 := by ring
        rw [this]
        calc t * t ^ 2 ≤ t * 1 := mul_le_mul_of_nonneg_left ht21 ht0
          _ = t := mul_one t
      have hrt : r2 * t ^ 3 ≤ (3 / 2) * t :=
        mul_le_mul hr2le h3 (pow_nonneg ht0 3) (by norm_num)
      have hpos : 0 ≤ sb * B := mul_nonneg hsb0 hB
      have := mul_le_mul_of_nonneg_left hrt hpos
      have e : (4 / 3) * r2 * sb * B * t ^ 3 = (4 / 3) * (sb * B * (r2 * t ^ 3)) := by ring
      have e' : 2 * B * sb * t = (4 / 3) * (sb * B * ((3 / 2) * t)) := by ring
      rw [e, e']; linarith
    have e3 : (4 / 9) * B ^ 2 * t ^ 4 ≤ (4 / 9) * B ^ 2 * t ^ 2 := by
      have h4 : t ^ 4 ≤ t ^ 2 := by
        have : t ^ 4 = t ^ 2 * t ^ 2 := by ring
        rw [this]
        calc t ^ 2 * t ^ 2 ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left ht21 (sq_nonneg t)
          _ = t ^ 2 := mul_one _
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have hsq' : |a + m ^ 2 - b| ≤ (3 / 2) * B * sb * t + (2 / 3) * B ^ 2 * t ^ 2 := by
      have : r2 * (B * sb * t) ≤ (3 / 2) * (B * sb * t) :=
        mul_le_mul_of_nonneg_right hr2le (by positivity)
      have e : r2 * B * sb * t = r2 * (B * sb * t) := by ring
      linarith
    rw [hexp] at hm2
    have p1 : 0 ≤ B * sb * t := by positivity
    have p2 : 0 ≤ B ^ 2 * t ^ 2 := by positivity
    have q1 : sb * B * t ^ 3 = (B * sb * t) * t ^ 2 := by ring
    linarith
  generalize hsbg : Real.sqrt b = sb at *
  rcases le_or_gt (B * t) sb with hcase | hcase
  · rcases eq_or_lt_of_le hsb0 with hsb | hsbpos
    · subst hsb
      have hBt : B * t = 0 := le_antisymm hcase (mul_nonneg hB ht0)
      have hzero : |a - b| ≤ 0 := by
        have : B ^ 2 * t ^ 2 = 0 := by rw [show B ^ 2 * t ^ 2 = (B * t) ^ 2 by ring, hBt]; ring
        have : B * 0 * t = 0 := by ring
        linarith
      have hab : a = b := by
        have := abs_nonneg (a - b)
        have h0 : |a - b| = 0 := le_antisymm hzero this
        linarith [abs_eq_zero.mp h0]
      have hb' : b = 0 := by rw [← hsb2]; ring
      rw [hab, hb', Real.sqrt_zero, sub_zero, abs_zero]; positivity
    · have hbpos : 0 < b := by rw [← hsb2]; positivity
      have hdiv := abs_sqrt_sub_sqrt_le_div ha0 hbpos
      rw [hsbg] at hdiv
      calc |Real.sqrt a - sb| ≤ |a - b| / sb := hdiv
        _ ≤ (6 * B * sb * t + 2 * B ^ 2 * t ^ 2) / sb :=
          div_le_div_of_nonneg_right hkey hsbpos.le
        _ ≤ 8 * B * t := by
          rw [div_le_iff₀ hsbpos]
          have hBt0 : 0 ≤ B * t := mul_nonneg hB ht0
          have : B ^ 2 * t ^ 2 ≤ B * t * sb := by
            rw [show B ^ 2 * t ^ 2 = (B * t) * (B * t) by ring]
            exact mul_le_mul_of_nonneg_left hcase hBt0
          have e : 8 * B * t * sb = 6 * B * sb * t + 2 * (B * t * sb) := by ring
          rw [e]; linarith
  · have hBt0 : 0 ≤ B * t := mul_nonneg hB ht0
    have hk : |a - b| ≤ 8 * B ^ 2 * t ^ 2 := by
      have : B * sb * t ≤ B ^ 2 * t ^ 2 := by
        rw [show B * sb * t = (B * t) * sb by ring, show B ^ 2 * t ^ 2 = (B * t) * (B * t) by ring]
        exact mul_le_mul_of_nonneg_left hcase.le hBt0
      linarith
    have hsa := abs_sqrt_sub_sqrt_le_sqrt_abs ha0 hb0
    rw [hsbg] at hsa
    calc |Real.sqrt a - sb| ≤ Real.sqrt |a - b| := hsa
      _ ≤ Real.sqrt ((3 * B * t) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have : 8 * B ^ 2 * t ^ 2 ≤ (3 * B * t) ^ 2 := by
            rw [show (3 * B * t) ^ 2 = 9 * (B ^ 2 * t ^ 2) by ring]
            have : 0 ≤ B ^ 2 * t ^ 2 := by positivity
            linarith
          linarith
      _ = 3 * B * t := Real.sqrt_sq (by positivity)
      _ ≤ 8 * B * t := by linarith

/-- (S): deterministic standard-deviation deviation bound from two Bernstein-type
hypotheses (mean of `f` and mean of the centered square `h = (f − E_p f)^2`). -/
theorem std_deviation_le (p p' : FiniteDistribution State) {f : State → ℝ} {B ℓ N : ℝ}
    (hB : 0 ≤ B) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) (hN : 0 < N) (hℓ0 : 0 ≤ ℓ)
    (hℓN : ℓ ≤ N)
    (hmean : |p'.expectation f - p.expectation f| ≤
      Real.sqrt (2 * ℓ * p.variance f / N) + 2 * B * ℓ / (3 * N))
    (hsq : |p'.expectation (fun x ↦ (f x - p.expectation f) ^ 2) -
        p.expectation (fun x ↦ (f x - p.expectation f) ^ 2)| ≤
      Real.sqrt (2 * ℓ * (B ^ 2 * p.variance f) / N) + 2 * B ^ 2 * ℓ / (3 * N)) :
    |Real.sqrt (p'.variance f) - Real.sqrt (p.variance f)| ≤ 8 * B * Real.sqrt (ℓ / N) := by
  have hb0 : 0 ≤ p.variance f := FiniteDistribution.variance_nonneg p f
  have hlN : 0 ≤ ℓ / N := div_nonneg hℓ0 hN.le
  have ht2 : Real.sqrt (ℓ / N) ^ 2 = ℓ / N := Real.sq_sqrt hlN
  have hrad1 : Real.sqrt (2 * ℓ * p.variance f / N) =
      Real.sqrt 2 * Real.sqrt (p.variance f) * Real.sqrt (ℓ / N) := by
    rw [show 2 * ℓ * p.variance f / N = 2 * p.variance f * (ℓ / N) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have hrad2 : Real.sqrt (2 * ℓ * (B ^ 2 * p.variance f) / N) =
      Real.sqrt 2 * B * Real.sqrt (p.variance f) * Real.sqrt (ℓ / N) := by
    rw [show 2 * ℓ * (B ^ 2 * p.variance f) / N = 2 * B ^ 2 * p.variance f * (ℓ / N) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq hB]
  have hlin : 2 * B * ℓ / (3 * N) = 2 / 3 * B * Real.sqrt (ℓ / N) ^ 2 := by
    rw [ht2]; field_simp
  have hlin2 : 2 * B ^ 2 * ℓ / (3 * N) = 2 / 3 * B ^ 2 * Real.sqrt (ℓ / N) ^ 2 := by
    rw [ht2]; field_simp
  rw [hrad1, hlin] at hmean
  rw [hrad2, hlin2] at hsq
  have hEh : p.expectation (fun x ↦ (f x - p.expectation f) ^ 2) = p.variance f :=
    (FiniteDistribution.variance_eq_expectation_centered_sq p f).symm
  have hEh' := expectation_sq_dev p' f (p.expectation f)
  rw [hEh, hEh'] at hsq
  apply std_core (FiniteDistribution.variance_nonneg p' f) hb0 hB
    (variance_le_sq_of_bounds p hf0 hfB) (Real.sqrt_nonneg _) _ hmean hsq
  rw [Real.sqrt_le_one]
  exact (div_le_one hN).mpr hℓN

end StatisticalRL.RobustRL.DRVI
