import Formalization.Probability.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Monotonicity of the variance-aware bonus function (`eq:nondecreasing-f-property`)

Remark 5.9 (`chapters/onlineRL.tex:1330–1332`) refers to the function
`f(p,v,n) = ⟨p,v⟩ + max{c₁ √(Var_p(v) log(1/δ')/n), c₁² H log(1/δ')/n}`
of `eq:monotone-function-f-pvn-ucbvi` (`chapters/onlineRL.tex:3299–3305`) and asserts that it is
non-decreasing in `v` on the box `0 ≤ v ≤ H` (`eq:nondecreasing-f-property`, `:3307–3311`).

The source proof (`:3392–3433`) differentiates `f` in one coordinate. Here we use an elementary
derivative-free route:

* `variance_sub_le_of_le`: for `0 ≤ v ≤ w ≤ H`, `Var(v) − Var(w) ≤ 2H(⟨p,w⟩ − ⟨p,v⟩)`;
* `expectation_add_mul_sqrt_variance_le`: if both `√Var(v)` and `√Var(w)` are at least the
  threshold `aH`, then `⟨p,v⟩ + a√Var(v) ≤ ⟨p,w⟩ + a√Var(w)`;
* in the mixed case the intermediate value theorem on the segment `v + t(w − v)` produces a point
  whose standard deviation is exactly the threshold.

The result is stated for every real `c₁` (for `c₁ ≤ 0` the maximum is always the second branch),
every `ι ≥ 0` and `n > 0`; no hypothesis beyond the printed domain is used.
-/

namespace StatisticalRL

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

/-- The variance-aware function `f(p,v,n)` of `eq:monotone-function-f-pvn-ucbvi`, written with
`ι = log(1/δ')`. -/
noncomputable def monotoneBonusFunction (p : FiniteDistribution Ω) (c₁ H ι n : ℝ)
    (v : Ω → ℝ) : ℝ :=
  p.expectation v + max (c₁ * Real.sqrt (p.variance v * ι / n)) (c₁ ^ 2 * H * ι / n)

/-- A finite probability vector has a nonempty carrier. -/
theorem nonempty_of_finiteDistribution (p : FiniteDistribution Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := p.sum_prob
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact zero_ne_one this

/-- Lemma A of the derivative-free route: moving up inside `[0, H]` can lower the variance by at
most `2H` times the increase of the mean. -/
theorem variance_sub_le_of_le (p : FiniteDistribution Ω) {v w : Ω → ℝ} {H : ℝ}
    (hv : ∀ x, 0 ≤ v x) (hvw : ∀ x, v x ≤ w x) (hw : ∀ x, w x ≤ H) :
    p.variance v - p.variance w ≤ 2 * H * (p.expectation w - p.expectation v) := by
  have h1 : p.expectation (fun x ↦ v x ^ 2) ≤ p.expectation (fun x ↦ w x ^ 2) :=
    p.expectation_mono fun x ↦ by nlinarith [hv x, hvw x]
  have h2 : p.expectation v ≤ p.expectation w := p.expectation_mono hvw
  have h3 : 0 ≤ p.expectation v := p.expectation_nonneg hv
  have h4 : p.expectation w ≤ H := p.expectation_le_const hw
  unfold variance
  nlinarith [mul_le_mul_of_nonneg_left (show p.expectation w + p.expectation v ≤ 2 * H by linarith)
    (sub_nonneg.mpr h2)]

/-- Lemma B: when both standard deviations are at least the threshold `a * H`, the √-branch is
monotone. -/
theorem expectation_add_mul_sqrt_variance_le (p : FiniteDistribution Ω) {v w : Ω → ℝ}
    {H a : ℝ} (ha : 0 ≤ a) (hv : ∀ x, 0 ≤ v x) (hvw : ∀ x, v x ≤ w x) (hw : ∀ x, w x ≤ H)
    (hsw : a * H ≤ Real.sqrt (p.variance w)) :
    p.expectation v + a * Real.sqrt (p.variance v) ≤
      p.expectation w + a * Real.sqrt (p.variance w) := by
  obtain ⟨x₀⟩ := p.nonempty_of_finiteDistribution
  have hH : 0 ≤ H := (hv x₀).trans ((hvw x₀).trans (hw x₀))
  have hA := p.variance_sub_le_of_le hv hvw hw
  have hD : 0 ≤ p.expectation w - p.expectation v := sub_nonneg.mpr (p.expectation_mono hvw)
  set sv := Real.sqrt (p.variance v) with hsv_def
  set sw := Real.sqrt (p.variance w) with hsw_def
  have hsv2 : sv ^ 2 = p.variance v := Real.sq_sqrt (p.variance_nonneg v)
  have hsw2 : sw ^ 2 = p.variance w := Real.sq_sqrt (p.variance_nonneg w)
  have hsw0 : 0 ≤ sw := Real.sqrt_nonneg _
  set D := p.expectation w - p.expectation v
  suffices a * (sv - sw) ≤ D by linarith
  by_cases hle : sv ≤ sw
  · nlinarith
  push_neg at hle
  rcases hH.lt_or_eq with hHpos | hH0
  · have hprod : (sv - sw) * (2 * a * H) ≤ (sv - sw) * (sv + sw) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hsq : (sv - sw) * (sv + sw) ≤ 2 * H * D := by
      have : (sv - sw) * (sv + sw) = sv ^ 2 - sw ^ 2 := by ring
      rw [this, hsv2, hsw2]
      exact hA
    have : 2 * H * (a * (sv - sw)) ≤ 2 * H * D := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · subst hH0
    have hsq : (sv - sw) * (sv + sw) ≤ 0 := by
      have : (sv - sw) * (sv + sw) = sv ^ 2 - sw ^ 2 := by ring
      rw [this, hsv2, hsw2]
      simpa using hA
    nlinarith

/-- The variance along a segment is continuous in the segment parameter. -/
theorem continuous_variance_segment (p : FiniteDistribution Ω) (v w : Ω → ℝ) :
    Continuous fun t : ℝ ↦ p.variance (fun x ↦ v x + t * (w x - v x)) := by
  unfold variance expectation
  fun_prop

/-- Normalised form of `eq:nondecreasing-f-property`: for `a ≥ 0`,
`⟨p,v⟩ + a·max(√Var(v), aH)` is non-decreasing on `0 ≤ v ≤ w ≤ H`. -/
theorem expectation_add_mul_max_sqrt_variance_mono (p : FiniteDistribution Ω) {v w : Ω → ℝ}
    {H a : ℝ} (ha : 0 ≤ a) (hv : ∀ x, 0 ≤ v x) (hvw : ∀ x, v x ≤ w x) (hw : ∀ x, w x ≤ H) :
    p.expectation v + a * max (Real.sqrt (p.variance v)) (a * H) ≤
      p.expectation w + a * max (Real.sqrt (p.variance w)) (a * H) := by
  obtain ⟨x₀⟩ := p.nonempty_of_finiteDistribution
  have hH : 0 ≤ H := (hv x₀).trans ((hvw x₀).trans (hw x₀))
  have haH : 0 ≤ a * H := mul_nonneg ha hH
  have hEvw : p.expectation v ≤ p.expectation w := p.expectation_mono hvw
  have hmaxw : a * (a * H) ≤ a * max (Real.sqrt (p.variance w)) (a * H) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) ha
  by_cases hsv : Real.sqrt (p.variance v) ≤ a * H
  · rw [max_eq_right hsv]
    linarith
  push_neg at hsv
  rw [max_eq_left hsv.le]
  by_cases hsw : a * H ≤ Real.sqrt (p.variance w)
  · rw [max_eq_left hsw]
    exact p.expectation_add_mul_sqrt_variance_le ha hv hvw hw hsw
  push_neg at hsw
  -- Mixed case: the intermediate value theorem on the segment from `v` to `w`.
  set g : ℝ → ℝ := fun t ↦ p.variance (fun x ↦ v x + t * (w x - v x)) with hg
  have hg0 : g 0 = p.variance v := by simp [hg]
  have hg1 : g 1 = p.variance w := by simp [hg]
  have hlow : g 1 ≤ (a * H) ^ 2 := by
    rw [hg1, ← Real.sq_sqrt (p.variance_nonneg w)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsw.le 2
  have hhigh : (a * H) ^ 2 ≤ g 0 := by
    rw [hg0, ← Real.sq_sqrt (p.variance_nonneg v)]
    exact pow_le_pow_left₀ haH hsv.le 2
  obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ :=
    intermediate_value_Icc' zero_le_one (p.continuous_variance_segment v w).continuousOn
      ⟨hlow, hhigh⟩
  set y : Ω → ℝ := fun x ↦ v x + t * (w x - v x) with hy
  have hvy : ∀ x, v x ≤ y x := fun x ↦ by
    have := mul_nonneg ht0 (sub_nonneg.mpr (hvw x))
    simp only [hy]; linarith
  have hyw : ∀ x, y x ≤ w x := fun x ↦ by
    have := mul_le_mul_of_nonneg_right ht1 (sub_nonneg.mpr (hvw x))
    simp only [hy]; linarith
  have hyH : ∀ x, y x ≤ H := fun x ↦ (hyw x).trans (hw x)
  have hsy : Real.sqrt (p.variance y) = a * H := by
    have : p.variance y = (a * H) ^ 2 := hgt
    rw [this, Real.sqrt_sq haH]
  have hstep := p.expectation_add_mul_sqrt_variance_le ha hv hvy hyH hsy.ge
  rw [hsy] at hstep
  have hEyw : p.expectation y ≤ p.expectation w := p.expectation_mono hyw
  linarith

/-- `eq:nondecreasing-f-property` (`chapters/onlineRL.tex:3307–3311`), vector form: for every
probability vector `p`, real `c₁`, `ι ≥ 0`, `n > 0` and `0 ≤ v ≤ w ≤ H` entrywise,
`f(p,v,n) ≤ f(p,w,n)`. -/
theorem monotoneBonusFunction_mono (p : FiniteDistribution Ω) {c₁ H ι n : ℝ}
    (hι : 0 ≤ ι) (hn : 0 < n) {v w : Ω → ℝ}
    (hv : ∀ x, 0 ≤ v x) (hvw : ∀ x, v x ≤ w x) (hw : ∀ x, w x ≤ H) :
    p.monotoneBonusFunction c₁ H ι n v ≤ p.monotoneBonusFunction c₁ H ι n w := by
  obtain ⟨x₀⟩ := p.nonempty_of_finiteDistribution
  have hH : 0 ≤ H := (hv x₀).trans ((hvw x₀).trans (hw x₀))
  have hL : 0 ≤ ι / n := div_nonneg hι hn.le
  have hEvw : p.expectation v ≤ p.expectation w := p.expectation_mono hvw
  unfold monotoneBonusFunction
  by_cases hc : c₁ ≤ 0
  · have hb : 0 ≤ c₁ ^ 2 * H * ι / n := by
      rw [mul_div_assoc]; positivity
    have hneg : ∀ u : Ω → ℝ, c₁ * Real.sqrt (p.variance u * ι / n) ≤ c₁ ^ 2 * H * ι / n :=
      fun u ↦ (mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)).trans hb
    rw [max_eq_right (hneg v), max_eq_right (hneg w)]
    linarith
  push_neg at hc
  set a := c₁ * Real.sqrt (ι / n) with ha_def
  have ha : 0 ≤ a := mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hsplit : ∀ u : Ω → ℝ,
      max (c₁ * Real.sqrt (p.variance u * ι / n)) (c₁ ^ 2 * H * ι / n) =
        a * max (Real.sqrt (p.variance u)) (a * H) := by
    intro u
    have h1 : c₁ * Real.sqrt (p.variance u * ι / n) = a * Real.sqrt (p.variance u) := by
      rw [mul_div_assoc, Real.sqrt_mul (p.variance_nonneg u), ha_def]
      ring
    have h2 : c₁ ^ 2 * H * ι / n = a * (a * H) := by
      have hs : Real.sqrt (ι / n) * Real.sqrt (ι / n) = ι / n := Real.mul_self_sqrt hL
      rw [ha_def]
      calc c₁ ^ 2 * H * ι / n = c₁ ^ 2 * H * (ι / n) := by ring
        _ = c₁ ^ 2 * H * (Real.sqrt (ι / n) * Real.sqrt (ι / n)) := by rw [hs]
        _ = c₁ * Real.sqrt (ι / n) * (c₁ * Real.sqrt (ι / n) * H) := by ring
    rw [h1, h2, mul_max_of_nonneg _ _ ha]
  rw [hsplit v, hsplit w]
  exact p.expectation_add_mul_max_sqrt_variance_mono ha hv hvw hw

/-- `eq:nondecreasing-f-property`, entrywise form as printed ("non-decreasing in each entry of
`v`"): changing one coordinate upward inside `[0, H]` does not decrease `f`. -/
theorem monotoneBonusFunction_update_mono [DecidableEq Ω] (p : FiniteDistribution Ω)
    {c₁ H ι n : ℝ} (hι : 0 ≤ ι) (hn : 0 < n) {v : Ω → ℝ} (hv : ∀ x, 0 ≤ v x)
    (hvH : ∀ x, v x ≤ H) (s : Ω) {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ H) :
    p.monotoneBonusFunction c₁ H ι n (Function.update v s y) ≤
      p.monotoneBonusFunction c₁ H ι n (Function.update v s z) := by
  apply p.monotoneBonusFunction_mono hι hn
  · intro x
    by_cases hx : x = s
    · subst hx; simpa using hy
    · simpa [Function.update_of_ne hx] using hv x
  · intro x
    by_cases hx : x = s
    · subst hx; simpa using hyz
    · simp [Function.update_of_ne hx]
  · intro x
    by_cases hx : x = s
    · subst hx; simpa using hz
    · simpa [Function.update_of_ne hx] using hvH x

end FiniteDistribution

end StatisticalRL
