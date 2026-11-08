import Formalization.RobustRL.DRVI.Thm72Numerics

/-!
# Constant arithmetic for corrected Theorem 7.4 (χ²; plan §3.8, re-derived)

`B = B' = 1/(1−γ)`, `clos = (√σ/2)B²`, `(S)` constant 8, `mx = max{√σ, σ}`,
`L = log(SAN/δ) ≥ 1/2` (for `SA ≥ 2`), `ℓ ≤ 9 L`, `c₂ = 10⁶`.
With `P = ℓ/(N(1−γ)³)`: `P ≤ 9ε²/10⁶` and `(mx/(1−γ))·P ≤ 9ε²/10⁶`.
-/

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

theorem le_of_sq_le_sq' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (pow_le_pow_iff_left₀ hx hy two_ne_zero).mp h

theorem chi_sqrt_eq {ℓ N g : ℝ} (hℓ : 0 ≤ ℓ) (hN : 0 < N) (hg : 0 < g) :
    Real.sqrt (ℓ / N) = Real.sqrt (ℓ / (N * g ^ 3)) * g * Real.sqrt g := by
  have e : ℓ / N = (ℓ / (N * g ^ 3)) * (g ^ 2 * g) := by field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hg.le]
  ring

/-- Scalar bound on the self-bounding expression, χ² instantiation. -/
theorem chi_selfBoundExpr_le {γ σ ε N L ℓ mx Ξ : ℝ} (hγ : 1 / 4 ≤ γ) (hγ1 : γ < 1)
    (hσ : 0 < σ) (hmx1 : Real.sqrt σ ≤ mx) (hmx2 : σ ≤ mx) (hε : 0 < ε)
    (hεg : ε ≤ 1 / (1 - γ)) (hL : 1 / 2 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 9 * L) (hN : 1 ≤ N)
    (hsample : 10 ^ 6 * (1 + mx / (1 - γ)) * L ≤ N * ((1 - γ) ^ 3 * ε ^ 2))
    (hΞ0 : 0 ≤ Ξ) (hΞ : Ξ ≤ 2 * (1 - γ) / N ^ 2) :
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
  have hNinv : 1 / N ^ 2 ≤ 2 * ε / 10 ^ 6 := by
    have h1' : 1 / N ^ 2 ≤ 1 / N := one_div_le_one_div_of_le hN0 (by nlinarith only [hN])
    have h2' : 1 / N ≤ 1 / (N * g ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : g ^ 2 ≤ 1 := by nlinarith only [hg, hg1]
      calc N * g ^ 2 ≤ N * 1 := mul_le_mul_of_nonneg_left this hN0.le
        _ = N := mul_one N
    linarith only [h1', h2', h1Ng2]
  have hΞ1 : Ξ ≤ 1 := by
    have hN2 : 2 ≤ N := by
      have : 10 ^ 6 / 2 ≤ N * g := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1Ng
        linarith only [h1Ng]
      nlinarith only [this, hg1, hg, hN0]
    have : 2 * g / N ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith only [hN2, hg1, hg]
    linarith only [this, hΞ]
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
  have hplan : Ξ / g ≤ 4 * ε / 10 ^ 6 := by
    have h1 : Ξ / g ≤ (2 * g / N ^ 2) / g := div_le_div_of_nonneg_right hΞ hg.le
    have e : (2 * g / N ^ 2) / g = 2 * (1 / N ^ 2) := by field_simp
    linarith only [h1, e, hNinv]
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

end StatisticalRL.RobustRL.DRVI

namespace StatisticalRL.RobustRL.DRVI

/-- `L = log(SAN/δ) ≥ log 2` when `SA ≥ 2`. -/
theorem chi_L_lower {S A N δ : ℝ} (hSA : 2 ≤ S * A) (hN : 1 ≤ N) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log 2 ≤ Real.log (S * A * N / δ) := by
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hδ]
  nlinarith

/-- `ℓ = log(16(N+1)² SA/δ) ≤ 9 L`. -/
theorem chi_ell_le {S A N δ : ℝ} (hSA : 2 ≤ S * A) (hN : 1 ≤ N) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log (4 * (4 * (N + 1) ^ 2) * (S * A) / δ) ≤ 9 * Real.log (S * A * N / δ) := by
  have hL := chi_L_lower hSA hN hδ hδ1
  set x := S * A * N / δ with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxN : N ≤ x := by
    rw [hxdef, le_div_iff₀ hδ]; nlinarith
  have hxSA : S * A / δ ≤ x := by
    rw [hxdef, div_le_div_iff₀ hδ hδ]
    have h1 : S * A * δ * 1 ≤ S * A * δ * N :=
      mul_le_mul_of_nonneg_left hN (by nlinarith)
    nlinarith only [h1]
  have hbound : 4 * (4 * (N + 1) ^ 2) * (S * A) / δ ≤ 64 * x ^ 3 := by
    have hN1 : (N + 1) ^ 2 ≤ 4 * N ^ 2 := by nlinarith only [hN]
    have e : 4 * (4 * (N + 1) ^ 2) * (S * A) / δ = 16 * (N + 1) ^ 2 * (S * A / δ) := by ring
    rw [e]
    have hSA0 : 0 ≤ S * A / δ := by positivity
    have h1 : 16 * (N + 1) ^ 2 * (S * A / δ) ≤ 16 * (4 * N ^ 2) * (S * A / δ) := by
      apply mul_le_mul_of_nonneg_right _ hSA0; linarith only [hN1]
    have h2 : N ^ 2 * (S * A / δ) ≤ x ^ 2 * x :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) hxN 2) hxSA hSA0 (by positivity)
    nlinarith only [h1, h2]
  have hpos : 0 < 4 * (4 * (N + 1) ^ 2) * (S * A) / δ := by positivity
  have hlog : Real.log (4 * (4 * (N + 1) ^ 2) * (S * A) / δ) ≤ Real.log 64 + 3 * Real.log x := by
    calc _ ≤ Real.log (64 * x ^ 3) := Real.log_le_log hpos hbound
      _ = Real.log 64 + 3 * Real.log x := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
  linarith only [hlog, h64, hL]

end StatisticalRL.RobustRL.DRVI
