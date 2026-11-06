import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Comparison of the two Bernoulli KL directions

For `1/2 ≤ q < p < 1`, `KL(Bern p ‖ Bern q) ≤ KL(Bern q ‖ Bern p)`, the middle inequality of
`lem:KL-quadratic-lower-bound` (`chapters/prelim.tex:1335–1346`). The proof follows the source
(lines 1378–1411): with `p = a + b`, `q = a - b`, the difference of the two divergences is a
function `g(a, b)` that is non-increasing in `b ≥ 0` and vanishes at `b = 0`.
-/

namespace StatisticalRL.Probability

/-- `KL(Bern p ‖ Bern q) ≤ KL(Bern q ‖ Bern p)` whenever `1/2 ≤ q < p < 1`. -/
theorem bernoulliKL_le_reverse (p q : ℝ) (hq : (1 : ℝ) / 2 ≤ q) (hqp : q < p) (hp : p < 1) :
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) := by
  set a : ℝ := (p + q) / 2 with ha
  set B : ℝ := (p - q) / 2 with hBdef
  have hB : 0 < B := by rw [hBdef]; linarith
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have h2a : 0 ≤ 2 * a - 1 := by rw [ha]; linarith
  have hpos : ∀ b ∈ Set.Icc (0 : ℝ) B,
      0 < a + b ∧ 0 < a - b ∧ 0 < 1 - a - b ∧ 0 < 1 - a + b := by
    intro b hb
    obtain ⟨h0, h1⟩ := hb
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ha] <;> rw [hBdef] at h1 <;> linarith
  let G : ℝ → ℝ := fun b => 2 * a * (Real.log (a + b) - Real.log (a - b)) +
    2 * (1 - a) * (Real.log (1 - a - b) - Real.log (1 - a + b))
  let G' : ℝ → ℝ := fun b => 2 * a * (1 / (a + b) + 1 / (a - b)) -
    2 * (1 - a) * (1 / (1 - a - b) + 1 / (1 - a + b))
  have hderiv : ∀ b ∈ Set.Icc (0 : ℝ) B, HasDerivAt G (G' b) b := by
    intro b hb
    obtain ⟨h1, h2, h3, h4⟩ := hpos b hb
    have d1 : HasDerivAt (fun x => Real.log (a + x)) (1 / (a + b)) b :=
      ((hasDerivAt_id' b).const_add a).log h1.ne'
    have d2 : HasDerivAt (fun x => Real.log (a - x)) (-1 / (a - b)) b :=
      ((hasDerivAt_id' b).const_sub a).log h2.ne'
    have d3 : HasDerivAt (fun x => Real.log (1 - a - x)) (-1 / (1 - a - b)) b :=
      ((hasDerivAt_id' b).const_sub (1 - a)).log h3.ne'
    have d4 : HasDerivAt (fun x => Real.log (1 - a + x)) (1 / (1 - a + b)) b :=
      ((hasDerivAt_id' b).const_add (1 - a)).log h4.ne'
    have hall := ((d1.sub d2).const_mul (2 * a)).add ((d3.sub d4).const_mul (2 * (1 - a)))
    refine hall.congr_deriv ?_
    simp only [G']
    ring
  have hG'neg : ∀ b ∈ Set.Icc (0 : ℝ) B, G' b ≤ 0 := by
    intro b hb
    obtain ⟨h1, h2, h3, h4⟩ := hpos b hb
    have e1 : 2 * a * (1 / (a + b) + 1 / (a - b)) = 4 * a ^ 2 / ((a + b) * (a - b)) := by
      field_simp
      try ring
    have e2 : 2 * (1 - a) * (1 / (1 - a - b) + 1 / (1 - a + b)) =
        4 * (1 - a) ^ 2 / ((1 - a - b) * (1 - a + b)) := by
      field_simp
      try ring
    simp only [G']
    rw [e1, e2, sub_nonpos, div_le_div_iff₀ (mul_pos h1 h2) (mul_pos h3 h4)]
    nlinarith [mul_nonneg (sq_nonneg b) h2a]
  have hcont : ContinuousOn G (Set.Icc (0 : ℝ) B) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hanti : AntitoneOn G (Set.Icc (0 : ℝ) B) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 B) hcont
      (fun x hx => (hderiv x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hG'neg x (interior_subset hx))
  have hGB : G B ≤ G 0 :=
    hanti (Set.left_mem_Icc.2 hB.le) (Set.right_mem_Icc.2 hB.le) hB.le
  have hG0 : G 0 = 0 := by simp [G]
  have hp' : a + B = p := by rw [ha, hBdef]; ring
  have hq' : a - B = q := by rw [ha, hBdef]; ring
  have h1p : 1 - a - B = 1 - p := by rw [ha, hBdef]; ring
  have h1q : 1 - a + B = 1 - q := by rw [ha, hBdef]; ring
  have hGval : G B = (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) -
      (q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))) := by
    simp only [G]
    rw [hp', hq', h1p, h1q]
    have hp1 : (0 : ℝ) < 1 - p := by linarith
    have hq1 : (0 : ℝ) < 1 - q := by linarith
    rw [Real.log_div hp0.ne' hq0.ne', Real.log_div hq0.ne' hp0.ne',
      Real.log_div hp1.ne' hq1.ne', Real.log_div hq1.ne' hp1.ne', ha]
    ring
  linarith

end StatisticalRL.Probability
