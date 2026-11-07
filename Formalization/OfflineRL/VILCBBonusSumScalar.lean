import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Theorem 6.3, Step 4: scalar bookkeeping

Source: `chapters/offlineRL.tex:1406–1623` (Step 4). Pure real-number lemmas:
* `state_term_le`: the per-state bound for `d⋆(s) b⋆(s)` covering both `S_small` (`:1423–1448`)
  and `S_large` (`:1451–1590`, with the count step `eq:infinite-N-to-d-bound`);
* `sum_sqrt_le`: Cauchy–Schwarz for `Σ_s √(a d(s) Var(s))` (`...-large-result0`, `:1517–1526`);
* `step4_abstract`: the summed bound `x ≤ 50Y + √(Y(192 + 384x))` with `x = ⟨d⋆, b⋆⟩` and
  `Y = c_b S C⋆ L₂/((1-γ)N)`, given the conclusion of Lemma 6.7 with `γ ≥ 1/2`;
* `self_bound`: `Y ≤ t²/10⁴`, `0 ≤ t ≤ 1` imply `2x ≤ t` (Step 4.3, `:1593–1623`).
-/

open scoped BigOperators

namespace StatisticalRL.OfflineVILCB.Theorem63

/-- Per-state bound (Step 4.1 and 4.2 together). Here `k = 1-γ`, `n` is the count at
`(s, π⋆(s))`, `db` the behaviour mass there, `d` the occupancy, `Ls = log(SN/δ) ≤ L₂`. -/
theorem state_term_le {d db C n N cb L L₂ Ls k var b : ℝ} (hN : 0 < N) (hk : 0 < k)
    (hC0 : 0 ≤ C) (hcb : 0 ≤ cb) (hL : 0 ≤ L) (hL₂ : 0 ≤ L₂) (hLs : Ls ≤ L₂)
    (hd0 : 0 ≤ d) (hdC : d ≤ C * db) (hvar : 0 ≤ var)
    (hbR : b ≤ 1 / k + 5 / N)
    (hcount : N * db / 12 ≤ max n ((2 / 3) * Ls))
    (hupper : 0 < n → b ≤ Real.sqrt (2 * cb * L * var / n) + 4 * cb * L / (k * n)) :
    d * b ≤ 8 * C * L₂ / (k * N) + 5 * d / N +
      Real.sqrt (24 * cb * C * L / N * (d * var)) + 48 * cb * C * L / (k * N) := by
  have hT1 : 0 ≤ 8 * C * L₂ / (k * N) := by positivity
  have hT2 : 0 ≤ 5 * d / N := by positivity
  have hT3 : 0 ≤ Real.sqrt (24 * cb * C * L / N * (d * var)) := Real.sqrt_nonneg _
  have hT4 : 0 ≤ 48 * cb * C * L / (k * N) := by positivity
  by_cases hsmall : N * db ≤ 8 * L₂
  · -- `S_small`
    have h1 : d * b ≤ d * (1 / k) + 5 * d / N := by
      have := mul_le_mul_of_nonneg_left hbR hd0
      have e : d * (1 / k + 5 / N) = d * (1 / k) + 5 * d / N := by ring
      linarith
    have h2 : d * (1 / k) ≤ 8 * C * L₂ / (k * N) := by
      have hdb : d ≤ C * (8 * L₂ / N) := by
        refine hdC.trans (mul_le_mul_of_nonneg_left ?_ hC0)
        rw [le_div_iff₀ hN]; linarith
      have e : 8 * C * L₂ / (k * N) = C * (8 * L₂ / N) * (1 / k) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hdb (by positivity)
    linarith
  · -- `S_large`
    push_neg at hsmall
    have hcnt : N * db / 12 ≤ n := by
      rcases le_max_iff.mp hcount with h | h
      · exact h
      · exfalso; linarith
    have hdb0 : 0 < db := by
      by_contra hneg; push_neg at hneg
      have : N * db ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hneg
      linarith
    have hn : 0 < n := by
      have : 0 < N * db / 12 := by positivity
      linarith
    have hdn : d * N ≤ 12 * C * n := by
      have h1 : d * N ≤ C * db * N := mul_le_mul_of_nonneg_right hdC hN.le
      have h2 : C * db * N ≤ C * (12 * n) := by
        rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC0; linarith
      linarith
    have hb := hupper hn
    have hsq : d * Real.sqrt (2 * cb * L * var / n) ≤
        Real.sqrt (24 * cb * C * L / N * (d * var)) := by
      have e0 : d * Real.sqrt (2 * cb * L * var / n) =
          Real.sqrt (d ^ 2 * (2 * cb * L * var / n)) := by
        rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd0]
      rw [e0]
      apply Real.sqrt_le_sqrt
      have e1 : d ^ 2 * (2 * cb * L * var / n) = (2 * cb * L * var * d) * (d / n) := by
        field_simp
      have e2 : 24 * cb * C * L / N * (d * var) = (2 * cb * L * var * d) * (12 * C / N) := by
        field_simp; ring
      rw [e1, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ hn hN]; linarith
    have hlin : d * (4 * cb * L / (k * n)) ≤ 48 * cb * C * L / (k * N) := by
      have e1 : d * (4 * cb * L / (k * n)) = (4 * cb * L / k) * (d / n) := by field_simp
      have e2 : 48 * cb * C * L / (k * N) = (4 * cb * L / k) * (12 * C / N) := by
        field_simp; ring
      rw [e1, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ hn hN]; linarith
    have h3 : d * b ≤ d * Real.sqrt (2 * cb * L * var / n) + d * (4 * cb * L / (k * n)) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hb hd0
    linarith

/-- Cauchy–Schwarz: `Σ_s √(a g(s)) ≤ √(a |S| Σ_s g(s))`. -/
theorem sum_sqrt_le {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    ∑ i, Real.sqrt (a * g i) ≤ Real.sqrt (a * Fintype.card ι * ∑ i, g i) := by
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset ι) (f := fun _ => a) (g := g)
    (fun _ => ha) hg
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  calc ∑ i, Real.sqrt (a * g i) = ∑ i, Real.sqrt a * Real.sqrt (g i) :=
        Finset.sum_congr rfl fun i _ => Real.sqrt_mul ha _
    _ ≤ Real.sqrt (Fintype.card ι * a) * Real.sqrt (∑ i, g i) := h
    _ = Real.sqrt (a * Fintype.card ι * ∑ i, g i) := by
        rw [← Real.sqrt_mul (by positivity), mul_comm (Fintype.card ι : ℝ) a]

/-- **Step 4, summed** (`eq:infinite-bernstein-small-result`, `eq:infinite-bernstein-large-result-all`):
with `x = Σ_s d(s) b(s)` and `Y = c_b |S| C L₂/(k N)`, `x ≤ 50 Y + √(Y (192 + 384 x))`. The input
`hlem67` is Lemma 6.7 with `γ ≥ 1/2` (`2/γ² ≤ 8`, `4/γ² ≤ 16`). -/
theorem step4_abstract {ι : Type*} [Fintype ι] [Nonempty ι] (d b var db n : ι → ℝ)
    {N C cb L L₂ Ls k : ℝ} (hN : 0 < N) (hk : 0 < k) (hk1 : k ≤ 1) (hC1 : 1 ≤ C)
    (hcb : 96 ≤ cb) (hL : 0 ≤ L) (hLL₂ : L ≤ L₂) (hL₂ : 1 / 2 ≤ L₂) (hLs : Ls ≤ L₂)
    (hd0 : ∀ s, 0 ≤ d s) (hdsum : ∑ s, d s = 1) (hdC : ∀ s, d s ≤ C * db s)
    (hvar : ∀ s, 0 ≤ var s) (hb0 : ∀ s, 0 ≤ b s) (hbR : ∀ s, b s ≤ 1 / k + 5 / N)
    (hcount : ∀ s, N * db s / 12 ≤ max (n s) ((2 / 3) * Ls))
    (hupper : ∀ s, 0 < n s →
      b s ≤ Real.sqrt (2 * cb * L * var s / n s) + 4 * cb * L / (k * n s))
    (hlem67 : ∑ s, d s * var s ≤ (8 + 16 * ∑ s, d s * b s) / k) :
    ∑ s, d s * b s ≤ 50 * (cb * Fintype.card ι * C * L₂ / (k * N)) +
      Real.sqrt ((cb * Fintype.card ι * C * L₂ / (k * N)) * (192 + 384 * ∑ s, d s * b s)) := by
  set x := ∑ s, d s * b s with hx
  set Sc : ℝ := (Fintype.card ι : ℝ) with hSc
  have hS1 : (1 : ℝ) ≤ Sc := by rw [hSc]; exact_mod_cast Fintype.card_pos
  have hC0 : 0 ≤ C := by linarith
  have hcb0 : 0 ≤ cb := by linarith
  have hL₂0 : 0 ≤ L₂ := by linarith
  set Y := cb * Sc * C * L₂ / (k * N) with hY
  have hx0 : 0 ≤ x := Finset.sum_nonneg fun s _ => mul_nonneg (hd0 s) (hb0 s)
  have hper := fun s => state_term_le (Ls := Ls) hN hk hC0 hcb0 hL hL₂0 hLs (hd0 s) (hdC s)
    (hvar s) (hbR s) (hcount s) (hupper s)
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hper s
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← hx] at hsum
  have h5 : ∑ s, 5 * d s / N = 5 / N := by
    have e : ∀ s, 5 * d s / N = 5 / N * d s := fun s => by ring
    simp_rw [e]
    rw [← Finset.mul_sum, hdsum, mul_one]
  rw [h5] at hsum
  -- Cauchy–Schwarz and Lemma 6.7
  have hcs := sum_sqrt_le (24 * cb * C * L / N) (by positivity) (fun s => d s * var s)
    (fun s => mul_nonneg (hd0 s) (hvar s))
  rw [← hSc] at hcs
  have hin : 24 * cb * C * L / N * Sc * ∑ s, d s * var s ≤ Y * (192 + 384 * x) := by
    have h1 : 24 * cb * C * L / N * Sc * ∑ s, d s * var s ≤
        24 * cb * C * L₂ / N * Sc * ((8 + 16 * x) / k) := by
      apply mul_le_mul _ hlem67 (Finset.sum_nonneg fun s _ => mul_nonneg (hd0 s) (hvar s))
        (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      apply div_le_div_of_nonneg_right _ hN.le
      apply mul_le_mul_of_nonneg_left hLL₂ (by positivity)
    have h2 : 24 * cb * C * L₂ / N * Sc * ((8 + 16 * x) / k) = Y * (192 + 384 * x) := by
      rw [hY]; field_simp; ring
    linarith
  have hsqrt : Real.sqrt (24 * cb * C * L / N * Sc * ∑ s, d s * var s) ≤
      Real.sqrt (Y * (192 + 384 * x)) := Real.sqrt_le_sqrt hin
  -- the remaining terms
  have hY1 : Sc * (8 * C * L₂ / (k * N)) ≤ Y := by
    have e : Sc * (8 * C * L₂ / (k * N)) = (8 / cb) * Y := by rw [hY]; field_simp
    rw [e]
    have : 8 / cb ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hY0 : 0 ≤ Y := by positivity
    nlinarith
  have hY2 : 5 / N ≤ Y := by
    rw [hY, div_le_div_iff₀ hN (by positivity)]
    have h1 : 48 ≤ cb * Sc * C * L₂ := by
      have : 96 * (1 / 2) ≤ cb * L₂ := by nlinarith
      have : cb * L₂ ≤ cb * Sc * C * L₂ := by
        have hcL : 0 ≤ cb * L₂ := by positivity
        have : 1 ≤ Sc * C := by nlinarith
        nlinarith
      linarith
    nlinarith
  have hY3 : Sc * (48 * cb * C * L / (k * N)) ≤ 48 * Y := by
    have e : 48 * Y = Sc * (48 * cb * C * L₂ / (k * N)) := by rw [hY]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left hLL₂ (by positivity)
  linarith

/-- **Step 4.3** self-bounding step: if `x ≤ 50Y + √(Y(192 + 384x))` with `Y ≤ t²/10⁴` and
`0 ≤ t ≤ 1`, then `2x ≤ t`. -/
theorem self_bound {x Y t : ℝ} (hx : 0 ≤ x) (hY : 0 ≤ Y) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hYt : Y ≤ t ^ 2 / 10000) (h : x ≤ 50 * Y + Real.sqrt (Y * (192 + 384 * x))) :
    2 * x ≤ t := by
  by_contra hlt
  push_neg at hlt
  have htt : t ^ 2 ≤ t := by nlinarith
  have h50 : 50 * Y ≤ x / 100 := by
    have : 50 * Y ≤ 50 * (t ^ 2 / 10000) := by linarith
    nlinarith
  set u := x - 50 * Y with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ Real.sqrt (Y * (192 + 384 * x)) := by linarith
  have hu2 : u ^ 2 ≤ Y * (192 + 384 * x) := (Real.le_sqrt hu0 (by positivity)).mp hu1
  have hrhs : Y * (192 + 384 * x) ≤ t ^ 2 / 10000 * (192 + 384 * x) :=
    mul_le_mul_of_nonneg_right hYt (by positivity)
  have hx0 : 0 < x := by linarith
  have ht2 : t ^ 2 < 4 * x ^ 2 := by nlinarith
  have hx3 : t ^ 2 * x ≤ 2 * x ^ 2 := by nlinarith
  have hu3 : (99 / 100 * x) ^ 2 ≤ u ^ 2 := by
    have : 99 / 100 * x ≤ u := by linarith
    nlinarith
  nlinarith

end StatisticalRL.OfflineVILCB.Theorem63
