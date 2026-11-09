import Formalization.RobustRL.DRVI.Thm74Numerics

/-!
# Constant arithmetic for Remark 7.2 (χ² oracle planners)

Source: `chapters/robust_RL.tex:453–457` (Theorem 7.4 :437–450). With `g = 1−γ`,
`L' = log(SAN/δ)` (the log of Theorem 7.4's sample-size condition) and
`L = log(SAN/((1−γ)δ)) ≤ L' + 1/g` (the log of the planner requirement), a planner error
`Ξ = c_opt·L/N²` satisfies `Ξ ≤ 1` and `Ξ/g ≤ ε/2` as soon as the sample-size condition holds with a
constant `c₂ ≥ 8 c_opt` (`chi_oracle_planning_bounds`). The self-bounding expression is re-split
into `2·selfBoundExpr ≤ ε/2` and `Ξ/g ≤ ε/2` (`chi_selfBoundExpr_le_of_planning`).

Technical debt: `chi_selfBoundExpr_le_of_planning` is a textual copy of `chi_selfBoundExpr_le`
with only the planning hypotheses generalized.
-/

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

/-- Scalar bound on the self-bounding expression, χ² instantiation, for a general planning error:
a copy of `chi_selfBoundExpr_le` in which the DRVI requirement `Ξ ≤ 2(1−γ)/N²` is replaced by
`Ξ ≤ 1` (so that `1 + Ξ ≤ 2` inside the square root of `selfBoundExpr`) and the separate additive
term `Ξ/(1−γ) ≤ ε/2`. The self-bounding part `2·selfBoundExpr` stays below `ε/2` (in fact below
`0.13 ε`), so the total is at most `ε`. -/
theorem chi_selfBoundExpr_le_of_planning {γ σ ε N L ℓ mx Ξ : ℝ} (hγ : 1 / 4 ≤ γ) (hγ1 : γ < 1)
    (hσ : 0 < σ) (hmx1 : Real.sqrt σ ≤ mx) (hmx2 : σ ≤ mx) (hε : 0 < ε)
    (hεg : ε ≤ 1 / (1 - γ)) (hL : 1 / 2 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 9 * L) (hN : 1 ≤ N)
    (hsample : 10 ^ 6 * (1 + mx / (1 - γ)) * L ≤ N * ((1 - γ) ^ 3 * ε ^ 2))
    (hΞ0 : 0 ≤ Ξ) (hΞ1 : Ξ ≤ 1) (hplan : Ξ / (1 - γ) ≤ ε / 2) :
    2 * selfBoundExpr γ (1 / (1 - γ)) Ξ (Real.sqrt (2 * ℓ / N))
        (Real.sqrt (2 * ℓ / N) * (1 / (N * (1 - γ)) +
            Real.sqrt (Real.sqrt σ / 2 * (1 / (1 - γ)) ^ 2)) +
          2 * (1 / (1 - γ)) * ℓ / (3 * N) +
          Real.sqrt σ * (8 * (1 / (1 - γ)) * Real.sqrt (ℓ / N)) +
          (4 + 2 * Real.sqrt σ) * (1 / (N * (1 - γ)))) +
      Ξ / (1 - γ) ≤ ε := by
  have hg : 0 < 1 - γ := by linarith
  have hN0 : 0 < N := by linarith
  have hsσ0 : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hmx0 : 0 < mx := lt_of_lt_of_le hsσ0 hmx1
  unfold selfBoundExpr
  rw [show 2 * ℓ / N = 2 * (ℓ / N) by ring, Real.sqrt_mul (by norm_num),
    chi_sqrt_eq hℓ0 hN0 hg]
  have hP0 : 0 ≤ ℓ / (N * (1 - γ) ^ 3) := by positivity
  generalize hgdef : 1 - γ = g at *
  have hg1 : g ≤ 3 / 4 := by linarith
  have hεg' : ε * g ≤ 1 := by rw [le_div_iff₀ hg] at hεg; linarith
  -- the two key ratios
  have hNg3 : 0 < N * g ^ 3 := by positivity
  have hLr : L / (N * g ^ 3) ≤ ε ^ 2 / 10 ^ 6 := by
    rw [div_le_div_iff₀ hNg3 (by positivity)]
    have : 10 ^ 6 * L ≤ 10 ^ 6 * (1 + mx / g) * L := by
      have : 0 ≤ mx / g := by positivity
      nlinarith only [this, hL]
    nlinarith only [this, hsample]
  have hLmr : (mx / g) * (L / (N * g ^ 3)) ≤ ε ^ 2 / 10 ^ 6 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hNg3 (by positivity)]
    have : 10 ^ 6 * ((mx / g) * L) ≤ 10 ^ 6 * (1 + mx / g) * L := by
      nlinarith only [hL]
    nlinarith only [this, hsample]
  set P := ℓ / (N * g ^ 3) with hPdef
  have hPL : P ≤ 9 * (L / (N * g ^ 3)) := by
    rw [hPdef, ← mul_div_assoc]; exact div_le_div_of_nonneg_right hℓ hNg3.le
  have hP : P ≤ 9 * (ε ^ 2 / 10 ^ 6) := by linarith only [hPL, hLr]
  have hmxg0 : 0 ≤ mx / g := by positivity
  have hPm : (mx / g) * P ≤ 9 * (ε ^ 2 / 10 ^ 6) := by
    have := mul_le_mul_of_nonneg_left hPL hmxg0
    linarith only [this, hLmr]
  -- consequences
  have h1Ng3 : 1 / (N * g ^ 3) ≤ 2 * ε ^ 2 / 10 ^ 6 := by
    have : 1 / (N * g ^ 3) ≤ 2 * (L / (N * g ^ 3)) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hNg3.le
    linarith only [this, hLr]
  have hgg : g ^ 2 ≤ g := by nlinarith only [hg, hg1]
  have hεg2 : ε * g ^ 2 ≤ 1 := by nlinarith only [hεg', hgg, hε]
  have h1Ng2 : 1 / (N * g ^ 2) ≤ 2 * ε / 10 ^ 6 := by
    have e : 1 / (N * g ^ 2) = g * (1 / (N * g ^ 3)) := by field_simp
    rw [e]
    have h := mul_le_mul_of_nonneg_left h1Ng3 hg.le
    have : g * (2 * ε ^ 2 / 10 ^ 6) ≤ 2 * ε / 10 ^ 6 := by
      have : g * (2 * ε ^ 2 / 10 ^ 6) = (2 * ε / 10 ^ 6) * (ε * g) := by ring
      rw [this]
      calc (2 * ε / 10 ^ 6) * (ε * g) ≤ (2 * ε / 10 ^ 6) * 1 :=
            mul_le_mul_of_nonneg_left hεg' (by positivity)
        _ = _ := mul_one _
    linarith only [h, this]
  have h1Ng : 1 / (N * g) ≤ 2 / 10 ^ 6 := by
    have e : 1 / (N * g) = g ^ 2 * (1 / (N * g ^ 3)) := by field_simp
    rw [e]
    have h := mul_le_mul_of_nonneg_left h1Ng3 (sq_nonneg g)
    have : g ^ 2 * (2 * ε ^ 2 / 10 ^ 6) ≤ 2 / 10 ^ 6 := by
      have : g ^ 2 * (2 * ε ^ 2 / 10 ^ 6) = (2 / 10 ^ 6) * (ε * g) ^ 2 := by ring
      rw [this]
      have : (ε * g) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hεg'
      nlinarith only [this]
    linarith only [h, this]
  have hsσNg2 : Real.sqrt σ / (N * g ^ 2) ≤ 2 * ε / 10 ^ 6 := by
    -- √σ/(N g²) = (√σ/g) g² /(N g³) ≤ (mx/g) g² ε² ... use (mx/g)·(1/(N g³)) ≤ (mx/g)·2L/(N g³)
    have e : Real.sqrt σ / (N * g ^ 2) = g ^ 2 * ((Real.sqrt σ / g) * (1 / (N * g ^ 3))) := by
      field_simp
    rw [e]
    have hs : Real.sqrt σ / g ≤ mx / g := div_le_div_of_nonneg_right hmx1 hg.le
    have h2 : (Real.sqrt σ / g) * (1 / (N * g ^ 3)) ≤ 2 * (ε ^ 2 / 10 ^ 6) := by
      have h3 : 1 / (N * g ^ 3) ≤ 2 * (L / (N * g ^ 3)) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hNg3.le
      have h4 := mul_le_mul hs h3 (by positivity) hmxg0
      nlinarith only [h4, hLmr]
    have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg g)
    have : g ^ 2 * (2 * (ε ^ 2 / 10 ^ 6)) ≤ 2 * ε / 10 ^ 6 := by
      have : g ^ 2 * (2 * (ε ^ 2 / 10 ^ 6)) = (2 * ε / 10 ^ 6) * (ε * g ^ 2) := by ring
      rw [this]
      calc (2 * ε / 10 ^ 6) * (ε * g ^ 2) ≤ (2 * ε / 10 ^ 6) * 1 :=
            mul_le_mul_of_nonneg_left hεg2 (by positivity)
        _ = _ := mul_one _
    linarith only [h5, this]
  -- named square roots
  have hsg0 : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hsg2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have hsg1 : Real.sqrt g ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsP0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hsP2 : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP0
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs20 : 0 < Real.sqrt 2 := by positivity
  have hsσ2 : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ.le
  have hsP : Real.sqrt P ≤ 3 * ε / 1000 := by
    apply le_of_sq_le_sq' hsP0 (by positivity)
    rw [hsP2]; nlinarith only [hP]
  -- term 1: √(2B(1+Ξ)/(γ²g²)) ≤ 8/(g√g)
  have hT1 : Real.sqrt (2 * (1 / g) * (1 + Ξ) / (γ ^ 2 * g ^ 2)) ≤ 8 / (g * Real.sqrt g) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, mul_pow, hsg2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hγ2 : 1 ≤ 16 * γ ^ 2 := by nlinarith only [hγ]
    have e : 2 * (1 / g) * (1 + Ξ) * (g ^ 2 * g) = 2 * (1 + Ξ) * g ^ 2 := by field_simp
    rw [e]
    have h4 : 2 * (1 + Ξ) ≤ 4 := by linarith only [hΞ1]
    have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
    calc 2 * (1 + Ξ) * g ^ 2 ≤ 4 * g ^ 2 := mul_le_mul_of_nonneg_right h4 hg2
      _ ≤ 8 ^ 2 * (γ ^ 2 * g ^ 2) := by nlinarith only [hγ2, hg2]
  have t1 : 2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g)) *
      Real.sqrt (2 * (1 / g) * (1 + Ξ) / (γ ^ 2 * g ^ 2)) ≤ 16 * Real.sqrt 2 * (3 * ε / 1000) := by
    have hpos : 0 ≤ 2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g)) := by positivity
    have h := mul_le_mul_of_nonneg_left hT1 hpos
    have e : 2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g)) * (8 / (g * Real.sqrt g)) =
        16 * Real.sqrt 2 * Real.sqrt P := by field_simp; ring
    have h2 : 16 * Real.sqrt 2 * Real.sqrt P ≤ 16 * Real.sqrt 2 * (3 * ε / 1000) :=
      mul_le_mul_of_nonneg_left hsP (by positivity)
    linarith only [h, e, h2]
  -- term 2
  have t2 : (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g)) ^ 2 * (2 * (1 / g) / (γ * g)) ≤
      144 * ε / 10 ^ 6 := by
    have e : (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g)) ^ 2 * (2 * (1 / g) / (γ * g)) =
        4 * P * g / γ := by
      rw [mul_pow, mul_pow, mul_pow, hs2, hsP2, hsg2]; field_simp; ring
    rw [e, div_le_iff₀ (by linarith)]
    have h := mul_le_mul_of_nonneg_right hP hg.le
    have h2 : 9 * (ε ^ 2 / 10 ^ 6) * g ≤ 9 * ε / 10 ^ 6 := by
      have : 9 * (ε ^ 2 / 10 ^ 6) * g = (9 * ε / 10 ^ 6) * (ε * g) := by ring
      rw [this]
      calc (9 * ε / 10 ^ 6) * (ε * g) ≤ (9 * ε / 10 ^ 6) * 1 :=
            mul_le_mul_of_nonneg_left hεg' (by positivity)
        _ = _ := mul_one _
    nlinarith only [h, h2, hγ, hε]
  have hs2le : Real.sqrt 2 ≤ 3 / 2 := by nlinarith only [hs2, hs20]
  have hσP : Real.sqrt σ / g * P ≤ 9 * (ε ^ 2 / 10 ^ 6) := by
    have : Real.sqrt σ / g ≤ mx / g := div_le_div_of_nonneg_right hmx1 hg.le
    exact (mul_le_mul_of_nonneg_right this hP0).trans hPm
  have hσP' : σ / g * P ≤ 9 * (ε ^ 2 / 10 ^ 6) := by
    have : σ / g ≤ mx / g := div_le_div_of_nonneg_right hmx2 hg.le
    exact (mul_le_mul_of_nonneg_right this hP0).trans hPm
  -- p1
  have p1 : 2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) * (1 / (N * g))) / g ≤
      ε / 10 ^ 6 := by
    have e : 2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) * (1 / (N * g))) / g =
        2 * Real.sqrt 2 * Real.sqrt P * Real.sqrt g * (1 / (N * g)) := by field_simp
    rw [e]
    have h1 : 2 * Real.sqrt 2 * Real.sqrt P * Real.sqrt g ≤ 2 * (3 / 2) * (3 * ε / 1000) * 1 := by
      have a := mul_le_mul hs2le hsP hsP0 (by norm_num)
      have b := mul_le_mul a hsg1 hsg0.le (by positivity)
      nlinarith only [b]
    have h2 := mul_le_mul h1 h1Ng (by positivity) (by positivity)
    nlinarith only [h2, hε]
  -- p2
  have p2 : 2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) *
      Real.sqrt (Real.sqrt σ / 2 * (1 / g) ^ 2)) / g ≤ 6 * ε / 1000 := by
    apply le_of_sq_le_sq' (by positivity) (by positivity)
    have hq0 : 0 ≤ Real.sqrt σ / 2 := by positivity
    rw [Real.sqrt_mul hq0, Real.sqrt_sq (by positivity)]
    have e : (2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) *
        (Real.sqrt (Real.sqrt σ / 2) * (1 / g))) / g) ^ 2 = 4 * (Real.sqrt σ / g * P) := by
      rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hs2, hsP2, hsg2,
        Real.sq_sqrt hq0]
      field_simp; ring
    rw [e]
    nlinarith only [hσP]
  -- p3
  have p3 : 2 * (2 * (1 / g) * ℓ / (3 * N)) / g ≤ 12 * ε / 10 ^ 6 := by
    have e : 2 * (2 * (1 / g) * ℓ / (3 * N)) / g = (4 / 3) * (P * g) := by
      rw [hPdef]; field_simp; ring
    rw [e]
    have h := mul_le_mul_of_nonneg_right hP hg.le
    have h2 : 9 * (ε ^ 2 / 10 ^ 6) * g ≤ 9 * ε / 10 ^ 6 := by
      have : 9 * (ε ^ 2 / 10 ^ 6) * g = (9 * ε / 10 ^ 6) * (ε * g) := by ring
      rw [this]
      calc (9 * ε / 10 ^ 6) * (ε * g) ≤ (9 * ε / 10 ^ 6) * 1 :=
            mul_le_mul_of_nonneg_left hεg' (by positivity)
        _ = _ := mul_one _
    nlinarith only [h, h2]
  -- p4
  have p4 : 2 * (Real.sqrt σ * (8 * (1 / g) * (Real.sqrt P * g * Real.sqrt g))) / g ≤
      48 * ε / 1000 := by
    apply le_of_sq_le_sq' (by positivity) (by positivity)
    have e : (2 * (Real.sqrt σ * (8 * (1 / g) * (Real.sqrt P * g * Real.sqrt g))) / g) ^ 2 =
        256 * (σ / g * P) := by
      simp only [div_pow, mul_pow, hsσ2, hsP2, hsg2]
      field_simp; ring
    rw [e]
    nlinarith only [hσP']
  -- p5
  have p5 : 2 * ((4 + 2 * Real.sqrt σ) * (1 / (N * g))) / g ≤ 24 * ε / 10 ^ 6 := by
    have e : 2 * ((4 + 2 * Real.sqrt σ) * (1 / (N * g))) / g =
        8 * (1 / (N * g ^ 2)) + 4 * (Real.sqrt σ / (N * g ^ 2)) := by field_simp; ring
    rw [e]
    linarith only [h1Ng2, hsσNg2]
  have ht1 : 16 * Real.sqrt 2 * (3 * ε / 1000) ≤ 16 * (3 / 2) * (3 * ε / 1000) :=
    mul_le_mul_of_nonneg_right (by linarith only [hs2le]) (by positivity)
  have hsplit : 2 * ((Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) * (1 / (N * g) +
      Real.sqrt (Real.sqrt σ / 2 * (1 / g) ^ 2)) + 2 * (1 / g) * ℓ / (3 * N) +
      Real.sqrt σ * (8 * (1 / g) * (Real.sqrt P * g * Real.sqrt g)) +
      (4 + 2 * Real.sqrt σ) * (1 / (N * g))) / g) =
      2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) * (1 / (N * g))) / g +
      2 * (Real.sqrt 2 * (Real.sqrt P * g * Real.sqrt g) *
        Real.sqrt (Real.sqrt σ / 2 * (1 / g) ^ 2)) / g +
      2 * (2 * (1 / g) * ℓ / (3 * N)) / g +
      2 * (Real.sqrt σ * (8 * (1 / g) * (Real.sqrt P * g * Real.sqrt g))) / g +
      2 * ((4 + 2 * Real.sqrt σ) * (1 / (N * g))) / g := by
    field_simp
  rw [hsplit]
  linarith only [t1, ht1, t2, p1, p2, p3, p4, p5, hplan, hε]

/-- `log(SAN/((1−γ)δ)) ≤ log(SAN/δ) + 1/(1−γ)`. -/
theorem chi_log_shift {x δ g : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hg : 0 < g) :
    Real.log (x / (g * δ)) ≤ Real.log (x / δ) + 1 / g := by
  have e : x / (g * δ) = x / δ * (1 / g) := by field_simp
  rw [e, Real.log_mul (by positivity) (by positivity)]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 / g by positivity)
  linarith

/-- The planner requirement of Remark 7.2 meets the two planning hypotheses of
`chi_selfBoundExpr_le_of_planning` once the sample-size constant is at least `8 c_opt`. -/
theorem chi_oracle_planning_bounds {γ ε N L L' mx c_opt c₂ : ℝ} (hγ : 1 / 4 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεg : ε ≤ 1 / (1 - γ)) (hN : 1 ≤ N) (hmx0 : 0 ≤ mx) (hc : 0 ≤ c_opt)
    (hc₂ : 8 * c_opt ≤ c₂) (hL' : 1 / 2 ≤ L') (hL : L ≤ L' + 1 / (1 - γ))
    (hsample : c₂ * (1 + mx / (1 - γ)) * L' ≤ N * ((1 - γ) ^ 3 * ε ^ 2)) :
    c_opt / N ^ 2 * L ≤ 1 ∧ c_opt / N ^ 2 * L / (1 - γ) ≤ ε / 2 := by
  have hg : 0 < 1 - γ := by linarith
  have hN0 : 0 < N := by linarith
  generalize hgdef : 1 - γ = g at *
  have hg1 : g ≤ 3 / 4 := by linarith
  have hεg' : ε * g ≤ 1 := by rw [le_div_iff₀ hg] at hεg; linarith
  have hc₂0 : 0 ≤ c₂ := by linarith
  have hmxg : 0 ≤ mx / g := by positivity
  have hL'0 : 0 ≤ L' := by linarith
  have hgne : g ≠ 0 := hg.ne'
  have hNne : N ≠ 0 := hN0.ne'
  have hS : c₂ * L' ≤ N * (g ^ 3 * ε ^ 2) := by
    have e : c₂ * (1 + mx / g) * L' = c₂ * L' + c₂ * (mx / g) * L' := by ring
    have h0 : 0 ≤ c₂ * (mx / g) * L' := mul_nonneg (mul_nonneg hc₂0 hmxg) hL'0
    linarith
  -- the two key bounds on `c_opt`
  have hA : c_opt * L' ≤ N * (g ^ 3 * ε ^ 2) / 8 := by
    have := mul_le_mul_of_nonneg_right hc₂ hL'0
    linarith
  have hB : c_opt ≤ N * (g ^ 3 * ε ^ 2) / 4 := by
    have := mul_le_mul_of_nonneg_left hL' hc
    linarith
  have hN2 : N ≤ N ^ 2 := by
    have := mul_le_mul_of_nonneg_left hN hN0.le
    rw [pow_two]; linarith
  have hgεg : g * (ε * g) ≤ 1 := by
    have := mul_le_mul (show g ≤ 1 by linarith) hεg' (by positivity) zero_le_one
    linarith
  have hgε2 : g ^ 2 * ε ^ 2 ≤ ε := by
    have e : g ^ 2 * ε ^ 2 = ε * (g * (ε * g)) := by ring
    have := mul_le_mul_of_nonneg_left hgεg hε.le
    linarith
  have hgε : g * ε ^ 2 ≤ ε := by
    have e : g * ε ^ 2 = ε * (ε * g) := by ring
    have := mul_le_mul_of_nonneg_left hεg' hε.le
    linarith
  -- term 1: `c_opt L'/(N² g) ≤ ε/8`
  have t1 : c_opt * L' / (N ^ 2 * g) ≤ ε / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have e : N * (g ^ 3 * ε ^ 2) = (N * g) * (g ^ 2 * ε ^ 2) := by ring
    have h1 : (N * g) * (g ^ 2 * ε ^ 2) ≤ (N * g) * ε :=
      mul_le_mul_of_nonneg_left hgε2 (by positivity)
    have h2 : (N * g) * ε ≤ (N ^ 2 * g) * ε := by
      apply mul_le_mul_of_nonneg_right _ hε.le
      exact mul_le_mul_of_nonneg_right hN2 hg.le
    have e2 : ε / 8 * (N ^ 2 * g) = (N ^ 2 * g) * ε / 8 := by ring
    rw [e2]
    linarith
  -- term 2: `c_opt/(N² g²) ≤ ε/4`
  have t2 : c_opt / (N ^ 2 * g ^ 2) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have e : N * (g ^ 3 * ε ^ 2) = (N * g ^ 2) * (g * ε ^ 2) := by ring
    have h1 : (N * g ^ 2) * (g * ε ^ 2) ≤ (N * g ^ 2) * ε :=
      mul_le_mul_of_nonneg_left hgε (by positivity)
    have h2 : (N * g ^ 2) * ε ≤ (N ^ 2 * g ^ 2) * ε := by
      apply mul_le_mul_of_nonneg_right _ hε.le
      exact mul_le_mul_of_nonneg_right hN2 (sq_nonneg g)
    have e2 : ε / 4 * (N ^ 2 * g ^ 2) = (N ^ 2 * g ^ 2) * ε / 4 := by ring
    rw [e2]
    linarith
  have hplan : c_opt / N ^ 2 * L / g ≤ ε / 2 := by
    have h1 : c_opt / N ^ 2 * L / g ≤ c_opt / N ^ 2 * (L' + 1 / g) / g := by
      apply div_le_div_of_nonneg_right _ hg.le
      exact mul_le_mul_of_nonneg_left hL (by positivity)
    have e : c_opt / N ^ 2 * (L' + 1 / g) / g =
        c_opt * L' / (N ^ 2 * g) + c_opt / (N ^ 2 * g ^ 2) := by
      field_simp
    linarith
  refine ⟨?_, hplan⟩
  have e : c_opt / N ^ 2 * L = g * (c_opt / N ^ 2 * L / g) := by
    rw [mul_div_cancel₀ _ hgne]
  rw [e]
  have h := mul_le_mul_of_nonneg_left hplan hg.le
  have h2 : g * (ε / 2) ≤ 1 / 2 := by linarith
  linarith

end StatisticalRL.RobustRL.DRVI
