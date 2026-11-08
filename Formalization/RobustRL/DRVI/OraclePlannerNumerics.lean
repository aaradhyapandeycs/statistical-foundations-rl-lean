import Formalization.RobustRL.DRVI.OraclePlanner

/-!
# Oracle planners for the TV DRVI bound: constant arithmetic (Remark 7.1)

The scalar bound `tv_selfBoundExpr_le_of_planning` is a copy of `tv_selfBoundExpr_le` (technical
debt, see `OraclePlanner`).

Source: arXiv:2610.41903v1, `chapters/robust_RL.tex:361–372` (`remark:tv-upper`). For every
`c_opt ≥ 0`, with `C₂ = max(10⁶, 2 c_opt)`: on the good event of Theorem 7.2 (probability
`≥ 1−δ`, independent of the planner), every deterministic `f` whose empirical robust value gap is
at most `c_opt (1−γ)² log(SAN/((1−γ)δ))/N` is `ε`-optimal for the true RMDP.
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

/-- Scalar bound on the self-bounding expression, TV instantiation, for a general planning
residual: a copy of `tv_selfBoundExpr_le` in which `Ξ ≤ 2(1−γ)/N²` is replaced by `Ξ ≤ 1` (all
that the `√(1+Ξ)` term `tv_T1` needs) and the planning term bound `Ξ/(1−γ) ≤ ε/2`. The
statistical terms total at most `≈ 0.473 ε`. -/
theorem tv_selfBoundExpr_le_of_planning {γ m σ ε N L ℓ B' Ξ : ℝ} (hγ : 1 / 4 ≤ γ) (hγ1 : γ < 1)
    (hm1 : 1 - γ ≤ m) (hm2 : m ≤ 1) (hσ0 : 0 ≤ σ) (hσm : σ ≤ m) (hε : 0 < ε)
    (hεm : ε ^ 2 * m ≤ 1) (hL : 1 / 4 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 17 * L) (hN : 1 ≤ N)
    (hsample : 10 ^ 6 * L ≤ N * ((1 - γ) ^ 2 * m * ε ^ 2)) (hB'0 : 0 ≤ B') (hB' : B' ≤ 4 / m)
    (hΞ0 : 0 ≤ Ξ) (hΞ1 : Ξ ≤ 1) (hplan : Ξ / (1 - γ) ≤ ε / 2) :
    2 * selfBoundExpr γ B' Ξ (Real.sqrt (2 * ℓ / N))
        (Real.sqrt (2 * ℓ / N) * (1 / (N * (1 - γ)) + Real.sqrt (σ * B' ^ 2)) +
          2 * (1 / (1 - γ)) * ℓ / (3 * N) + 4 * (1 / (N * (1 - γ)))) +
      Ξ / (1 - γ) ≤ ε := by
  have hg : 0 < 1 - γ := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le hg hm1
  have hN0 : 0 < N := by linarith
  unfold selfBoundExpr
  rw [sqrt_two_ell_eq hℓ0 hN0 hm0 hg]
  have hr0 : 0 ≤ Real.sqrt (2 * (ℓ / (N * m * (1 - γ) ^ 2))) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ ℓ / (N * m * (1 - γ) ^ 2) := by positivity
  generalize hgdef : 1 - γ = g at *
  obtain ⟨hεg, hεm', hNg2, hNg, _hNinv⟩ :=
    numerics_basic hg (by linarith) hm1 hm2 hε hεm hL hN hsample
  have hQ : L / (N * m * g ^ 2) ≤ ε ^ 2 / 10 ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hsample]
  have hq : ℓ / (N * m * g ^ 2) ≤ 17 * (ε ^ 2 / 10 ^ 6) := by
    have : ℓ / (N * m * g ^ 2) ≤ 17 * (L / (N * m * g ^ 2)) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hℓ (by positivity)
    linarith only [this, hQ]
  have hr := small_r hq0 hq le_rfl hε
  have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hsm2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0.le
  have hsm1 : Real.sqrt m ≤ 1 := Real.sqrt_le_one.mpr hm2
  have hsσ : Real.sqrt σ ≤ Real.sqrt m := Real.sqrt_le_sqrt hσm
  have hB'sq : Real.sqrt (σ * B' ^ 2) ≤ 4 / Real.sqrt m := by
    rw [Real.sqrt_mul hσ0, Real.sqrt_sq hB'0]
    calc Real.sqrt σ * B' ≤ Real.sqrt m * (4 / m) := mul_le_mul hsσ hB' hB'0 hsm0.le
      _ = 4 * (Real.sqrt m / m) := by ring
      _ = 4 / Real.sqrt m := by rw [Real.sqrt_div_self']; ring
  have hT1 := tv_T1 hB'0 hB' hΞ0 hΞ1 hm0 hγ hg hsm0 hsm2
  have hT2 := tv_T2 (r := Real.sqrt (2 * (ℓ / (N * m * g ^ 2)))) hB'0 hB' hm0 hγ hg hsm2
  generalize Real.sqrt (2 * (ℓ / (N * m * g ^ 2))) = r at *
  generalize Real.sqrt m = sm at *
  -- term 1
  have t1 : 2 * (r * sm * g) * Real.sqrt (2 * B' * (1 + Ξ) / (γ ^ 2 * g ^ 2)) ≤ 32 * r := by
    have := mul_le_mul_of_nonneg_left hT1 (by positivity : 0 ≤ 2 * (r * sm * g))
    have e : 2 * (r * sm * g) * (16 / (sm * g)) = 32 * r := by field_simp; ring
    linarith only [this, e]
  -- term 2
  have hr2 : r ^ 2 * g ≤ r / 170 := by
    have h1 : r ^ 2 * g ≤ r * (ε / 170) * g := by
      have : r ^ 2 ≤ r * (ε / 170) := by nlinarith only [hr, hr0]
      exact mul_le_mul_of_nonneg_right this hg.le
    have h2 : r * (ε / 170) * g = (r / 170) * (ε * g) := by ring
    have h3 : (r / 170) * (ε * g) ≤ (r / 170) * 1 :=
      mul_le_mul_of_nonneg_left hεg (by positivity)
    linarith only [h1, h2, h3]
  -- term 3 pieces
  have t3a : 2 * ((r * sm * g) * (1 / (N * g))) / g ≤ 2 * r * (4 / 10 ^ 6) := by
    have e : 2 * ((r * sm * g) * (1 / (N * g))) / g = 2 * r * (sm * (1 / (N * g))) := by
      field_simp
    rw [e]
    have : sm * (1 / (N * g)) ≤ 4 / 10 ^ 6 := by
      calc sm * (1 / (N * g)) ≤ 1 * (1 / (N * g)) :=
            mul_le_mul_of_nonneg_right hsm1 (by positivity)
        _ ≤ _ := by linarith only [hNg]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have t3b : 2 * ((r * sm * g) * Real.sqrt (σ * B' ^ 2)) / g ≤ 8 * r := by
    have h := mul_le_mul_of_nonneg_left hB'sq (by positivity : 0 ≤ r * sm * g)
    have e : (r * sm * g) * (4 / sm) = 4 * r * g := by field_simp
    have h2 : 2 * ((r * sm * g) * Real.sqrt (σ * B' ^ 2)) / g ≤ 2 * (4 * r * g) / g :=
      div_le_div_of_nonneg_right (by linarith only [h, e]) hg.le
    have e2 : 2 * (4 * r * g) / g = 8 * r := by field_simp; ring
    linarith only [h2, e2]
  have t3c : 2 * (2 * (1 / g) * ℓ / (3 * N)) / g ≤ (4 / 3) * 17 * ε / 10 ^ 6 := by
    have e : 2 * (2 * (1 / g) * ℓ / (3 * N)) / g = (4 / 3) * (ℓ / (N * m * g ^ 2)) * m := by
      field_simp; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hq hm0.le
    have h2 : 17 * (ε ^ 2 / 10 ^ 6) * m = 17 / 10 ^ 6 * (ε ^ 2 * m) := by ring
    have h3 : 17 / 10 ^ 6 * (ε ^ 2 * m) ≤ 17 / 10 ^ 6 * ε :=
      mul_le_mul_of_nonneg_left hεm' (by norm_num)
    nlinarith only [h1, h2, h3]
  have t3d : 2 * (4 * (1 / (N * g))) / g ≤ 8 * (4 * ε / 10 ^ 6) := by
    have e : 2 * (4 * (1 / (N * g))) / g = 8 * (1 / (N * g ^ 2)) := by field_simp; ring
    rw [e]; linarith only [hNg2]
  have hsplit : 2 * (((r * sm * g) * (1 / (N * g) + Real.sqrt (σ * B' ^ 2)) +
      2 * (1 / g) * ℓ / (3 * N) + 4 * (1 / (N * g))) / g) =
      2 * ((r * sm * g) * (1 / (N * g))) / g + 2 * ((r * sm * g) * Real.sqrt (σ * B' ^ 2)) / g +
        2 * (2 * (1 / g) * ℓ / (3 * N)) / g + 2 * (4 * (1 / (N * g))) / g := by
    field_simp
  rw [hsplit]
  linarith only [t1, hT2, hr2, t3a, t3b, t3c, t3d, hplan, hr, hε]

/-- The oracle requirement `Ξ = c (1−γ)² L / N` is small under the sample-size condition
`C L ≤ N (1−γ)² m ε²` with `C ≥ 2c`: `0 ≤ Ξ ≤ 1` and `Ξ/(1−γ) ≤ ε/2`. -/
theorem oracle_planning_bounds {c C L g m ε N : ℝ} (hc : 0 ≤ c) (hC : 2 * c ≤ C) (hC0 : 0 < C)
    (hg : 0 < g) (hg1 : g ≤ 1) (hm0 : 0 ≤ m) (hε : 0 < ε) (hεm1 : ε ^ 2 * m ≤ 1)
    (hεm : ε ^ 2 * m ≤ ε) (hL : 0 ≤ L) (hN : 0 < N)
    (hsample : C * L ≤ N * (g ^ 2 * m * ε ^ 2)) :
    0 ≤ c * g ^ 2 / N * L ∧ c * g ^ 2 / N * L ≤ 1 ∧ c * g ^ 2 / N * L / g ≤ ε / 2 := by
  set Ξ := c * g ^ 2 / N * L with hΞdef
  have hΞ0 : 0 ≤ Ξ := by positivity
  have hΞN : Ξ * N = c * g ^ 2 * L := by rw [hΞdef]; field_simp
  -- C Ξ ≤ c g⁴ m ε²
  have hkey : C * Ξ ≤ c * g ^ 4 * (ε ^ 2 * m) := by
    have h1 : c * g ^ 2 * (C * L) ≤ c * g ^ 2 * (N * (g ^ 2 * m * ε ^ 2)) :=
      mul_le_mul_of_nonneg_left hsample (by positivity)
    have h2 : C * Ξ * N ≤ c * g ^ 4 * (ε ^ 2 * m) * N := by
      have e1 : C * Ξ * N = c * g ^ 2 * (C * L) := by rw [mul_assoc, hΞN]; ring
      have e2 : c * g ^ 4 * (ε ^ 2 * m) * N = c * g ^ 2 * (N * (g ^ 2 * m * ε ^ 2)) := by ring
      rw [e1, e2]; exact h1
    exact le_of_mul_le_mul_right h2 hN
  have hg4 : g ^ 4 ≤ 1 := pow_le_one₀ hg.le hg1
  have hg3 : g ^ 3 ≤ 1 := pow_le_one₀ hg.le hg1
  have hεm0 : 0 ≤ ε ^ 2 * m := by positivity
  refine ⟨hΞ0, ?_, ?_⟩
  · have h1 : c * g ^ 4 * (ε ^ 2 * m) ≤ c * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg4 hc) hεm1 hεm0 (by positivity)
    have h2 : C * Ξ ≤ C * 1 := by nlinarith
    exact le_of_mul_le_mul_left h2 hC0
  · rw [div_le_iff₀ hg]
    have h1 : c * g ^ 4 * (ε ^ 2 * m) = (c * g) * (g ^ 3 * (ε ^ 2 * m)) := by ring
    have h2 : g ^ 3 * (ε ^ 2 * m) ≤ 1 * ε :=
      mul_le_mul hg3 hεm hεm0 zero_le_one
    have h3 : C * Ξ ≤ (c * g) * ε := by
      rw [h1] at hkey
      have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ c * g)
      linarith
    have h4 : (c * g) * ε ≤ C * (ε / 2 * g) := by
      have : 2 * c * (g * ε) ≤ C * (g * ε) := mul_le_mul_of_nonneg_right hC (by positivity)
      nlinarith
    exact le_of_mul_le_mul_left (h3.trans h4) hC0

end StatisticalRL.RobustRL.DRVI
