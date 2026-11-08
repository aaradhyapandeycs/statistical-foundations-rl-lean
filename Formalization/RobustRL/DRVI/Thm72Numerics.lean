import Formalization.RobustRL.DRVI.GapBound

/-!
# Constant arithmetic for corrected Theorem 7.2 (TV; plan §3.8, re-derived)

Pure real inequalities: with `C₂ = 10⁶`, the self-bounding expression and the planning term are
below `ε` on the printed parameter range. `m = max{1−γ, σ}`, `B' = 1/(1−γ+γσ) ≤ 4/m`,
`ℓ ≤ 17 L`, `L = log(SAN/((1−γ)δ)) ≥ 1/4`.
-/

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

theorem le_one_of_sq_le_one {x : ℝ} (_hx : 0 ≤ x) (h : x ^ 2 ≤ 1) : x ≤ 1 := by
  nlinarith only [h]

/-- Parameter consequences used by both instantiations. -/
theorem numerics_basic {g m ε N L : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hgm : g ≤ m) (hm2 : m ≤ 1)
    (hε : 0 < ε) (hεm : ε ^ 2 * m ≤ 1) (hL : 1 / 4 ≤ L) (hN : 1 ≤ N)
    (hsample : 10 ^ 6 * L ≤ N * (g ^ 2 * m * ε ^ 2)) :
    ε * g ≤ 1 ∧ ε ^ 2 * m ≤ ε ∧ 1 / (N * g ^ 2) ≤ 4 * ε / 10 ^ 6 ∧ 1 / (N * g) ≤ 4 / 10 ^ 6 ∧
      1 / N ^ 2 ≤ 4 * ε / 10 ^ 6 := by
  have hm0 : 0 < m := lt_of_lt_of_le hg hgm
  have hN0 : 0 < N := by linarith
  have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hsm2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0.le
  have hsm1 : Real.sqrt m ≤ 1 := Real.sqrt_le_one.mpr hm2
  have hgsm : g ≤ Real.sqrt m := by
    calc g = Real.sqrt (g ^ 2) := (Real.sqrt_sq hg.le).symm
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt (by nlinarith only [hg, hg1, hgm])
  have h1 : ε * Real.sqrt m ≤ 1 := by
    apply le_one_of_sq_le_one (by positivity)
    rw [mul_pow, hsm2]; exact hεm
  have hεg : ε * g ≤ 1 := (mul_le_mul_of_nonneg_left hgsm hε.le).trans h1
  have hεm' : ε ^ 2 * m ≤ ε := by
    have e : ε ^ 2 * m = ε * ((ε * Real.sqrt m) * Real.sqrt m) := by
      rw [show ε ^ 2 * m = ε ^ 2 * Real.sqrt m ^ 2 by rw [hsm2]]; ring
    rw [e]
    have : (ε * Real.sqrt m) * Real.sqrt m ≤ 1 :=
      (mul_le_mul h1 hsm1 hsm0.le zero_le_one).trans (by norm_num)
    calc ε * ((ε * Real.sqrt m) * Real.sqrt m) ≤ ε * 1 := mul_le_mul_of_nonneg_left this hε.le
      _ = ε := mul_one ε
  have hNg2 : 1 / (N * g ^ 2) ≤ 4 * ε / 10 ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hX : 0 ≤ N * g ^ 2 := by positivity
    have h4 : (1 : ℝ) ≤ 4 * L := by linarith
    have hprod := mul_le_mul_of_nonneg_left hεm' hX
    have : 10 ^ 6 * L ≤ (N * g ^ 2) * ε := by
      have e : N * (g ^ 2 * m * ε ^ 2) = (N * g ^ 2) * (ε ^ 2 * m) := by ring
      linarith only [hsample, hprod, e]
    nlinarith only [this, h4, hX, hε]
  have hNg : 1 / (N * g) ≤ 4 / 10 ^ 6 := by
    have hgmε : g * (m * ε ^ 2) ≤ 1 := by
      have h2 : m * ε ^ 2 ≤ 1 := by linarith only [hεm]
      calc g * (m * ε ^ 2) ≤ 1 * 1 :=
            mul_le_mul hg1 h2 (by positivity) zero_le_one
        _ = 1 := by ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hNg0 : 0 ≤ N * g := by positivity
    have : 10 ^ 6 * L ≤ N * g * (g * (m * ε ^ 2)) := by
      have e : N * (g ^ 2 * m * ε ^ 2) = N * g * (g * (m * ε ^ 2)) := by ring
      linarith only [hsample, e]
    have h3 : N * g * (g * (m * ε ^ 2)) ≤ N * g := by
      calc N * g * (g * (m * ε ^ 2)) ≤ N * g * 1 := mul_le_mul_of_nonneg_left hgmε hNg0
        _ = N * g := mul_one _
    nlinarith only [this, h3, hL]
  have hNinv : 1 / N ^ 2 ≤ 4 * ε / 10 ^ 6 := by
    have h1' : 1 / N ^ 2 ≤ 1 / N := one_div_le_one_div_of_le hN0 (by nlinarith only [hN])
    have h2' : 1 / N ≤ 1 / (N * g ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : g ^ 2 ≤ 1 := by nlinarith only [hg, hg1]
      calc N * g ^ 2 ≤ N * 1 := mul_le_mul_of_nonneg_left this hN0.le
        _ = N := mul_one N
    linarith only [h1', h2', hNg2]
  exact ⟨hεg, hεm', hNg2, hNg, hNinv⟩

/-- `√(2ℓ/N) = r √m g` with `r = √(2q)`, `q = ℓ/(N m g²)`. -/
theorem sqrt_two_ell_eq {ℓ N m g : ℝ} (hℓ : 0 ≤ ℓ) (hN : 0 < N) (hm : 0 < m) (hg : 0 < g) :
    Real.sqrt (2 * ℓ / N) = Real.sqrt (2 * (ℓ / (N * m * g ^ 2))) * Real.sqrt m * g := by
  have e : 2 * ℓ / N = (2 * (ℓ / (N * m * g ^ 2))) * (m * g ^ 2) := by
    field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul hm.le, Real.sqrt_sq hg.le]
  ring

theorem small_r {q ε K : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ K * (ε ^ 2 / 10 ^ 6)) (hK : K ≤ 17)
    (hε : 0 < ε) : Real.sqrt (2 * q) ≤ ε / 170 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have : q ≤ 17 * (ε ^ 2 / 10 ^ 6) :=
    hq.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  nlinarith only [this, hε]

/-- First self-bounding term (TV). -/
theorem tv_T1 {B' Ξ m γ g sm : ℝ} (hB'0 : 0 ≤ B') (hB' : B' ≤ 4 / m) (hΞ0 : 0 ≤ Ξ)
    (hΞ1 : Ξ ≤ 1) (hm0 : 0 < m) (hγ : 1 / 4 ≤ γ) (hg : 0 < g) (hsm0 : 0 < sm)
    (hsm2 : sm ^ 2 = m) :
    Real.sqrt (2 * B' * (1 + Ξ) / (γ ^ 2 * g ^ 2)) ≤ 16 / (sm * g) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hγ0 : 0 < γ := by linarith
  rw [div_pow, mul_pow, hsm2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hBm : B' * m ≤ 4 := by
    have := mul_le_mul_of_nonneg_right hB' hm0.le
    rwa [div_mul_cancel₀ _ hm0.ne'] at this
  have h1 : 2 * B' * (1 + Ξ) * m ≤ 16 := by
    have : 2 * (B' * m) * (1 + Ξ) ≤ 2 * 4 * 2 :=
      mul_le_mul (by linarith only [hBm]) (by linarith only [hΞ1]) (by linarith only [hΞ0])
        (by norm_num)
    linarith only [this]
  have hγ2 : 16 ≤ 16 ^ 2 * γ ^ 2 := by nlinarith only [hγ]
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  calc 2 * B' * (1 + Ξ) * (m * g ^ 2) = (2 * B' * (1 + Ξ) * m) * g ^ 2 := by ring
    _ ≤ 16 * g ^ 2 := mul_le_mul_of_nonneg_right h1 hg2
    _ ≤ (16 ^ 2 * γ ^ 2) * g ^ 2 := mul_le_mul_of_nonneg_right hγ2 hg2
    _ = 16 ^ 2 * (γ ^ 2 * g ^ 2) := by ring

/-- Second self-bounding term (TV). -/
theorem tv_T2 {B' m γ g sm r : ℝ} (hB'0 : 0 ≤ B') (hB' : B' ≤ 4 / m) (hm0 : 0 < m)
    (hγ : 1 / 4 ≤ γ) (hg : 0 < g) (hsm2 : sm ^ 2 = m) :
    (r * sm * g) ^ 2 * (2 * B' / (γ * g)) ≤ 32 * r ^ 2 * g := by
  have hγ0 : 0 < γ := by linarith
  have hBm : B' * m ≤ 4 := by
    have := mul_le_mul_of_nonneg_right hB' hm0.le
    rwa [div_mul_cancel₀ _ hm0.ne'] at this
  have e : (r * sm * g) ^ 2 * (2 * B' / (γ * g)) = r ^ 2 * g * (2 * (B' * m) / γ) := by
    rw [mul_pow, mul_pow, hsm2]; field_simp
  rw [e]
  have h : 2 * (B' * m) / γ ≤ 32 := by
    rw [div_le_iff₀ hγ0]; nlinarith only [hBm, hγ, hB'0, hm0]
  have hr : 0 ≤ r ^ 2 * g := by positivity
  calc r ^ 2 * g * (2 * (B' * m) / γ) ≤ r ^ 2 * g * 32 := mul_le_mul_of_nonneg_left h hr
    _ = 32 * r ^ 2 * g := by ring

/-- Scalar bound on the self-bounding expression, TV instantiation. -/
theorem tv_selfBoundExpr_le {γ m σ ε N L ℓ B' Ξ : ℝ} (hγ : 1 / 4 ≤ γ) (hγ1 : γ < 1)
    (hm1 : 1 - γ ≤ m) (hm2 : m ≤ 1) (hσ0 : 0 ≤ σ) (hσm : σ ≤ m) (hε : 0 < ε)
    (hεm : ε ^ 2 * m ≤ 1) (hL : 1 / 4 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 17 * L) (hN : 1 ≤ N)
    (hsample : 10 ^ 6 * L ≤ N * ((1 - γ) ^ 2 * m * ε ^ 2)) (hB'0 : 0 ≤ B') (hB' : B' ≤ 4 / m)
    (hΞ0 : 0 ≤ Ξ) (hΞ : Ξ ≤ 2 * (1 - γ) / N ^ 2) :
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
  obtain ⟨hεg, hεm', hNg2, hNg, hNinv⟩ :=
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
  have hΞ1 : Ξ ≤ 1 := by
    have : 2 * g / N ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hg1 : g ≤ 1 := by linarith
      have hNg' : 10 ^ 6 / 4 ≤ N * g := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)] at hNg
        linarith only [hNg]
      have hN2 : 2 ≤ N := by nlinarith only [hNg', hg1, hg, hN0]
      nlinarith only [hN2, hg1, hg]
    linarith only [this, hΞ]
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
  have hplan : Ξ / g ≤ 2 * (4 * ε / 10 ^ 6) := by
    have h1 : Ξ / g ≤ (2 * g / N ^ 2) / g := div_le_div_of_nonneg_right hΞ hg.le
    have e : (2 * g / N ^ 2) / g = 2 * (1 / N ^ 2) := by field_simp
    linarith only [h1, e, hNinv]
  have hsplit : 2 * (((r * sm * g) * (1 / (N * g) + Real.sqrt (σ * B' ^ 2)) +
      2 * (1 / g) * ℓ / (3 * N) + 4 * (1 / (N * g))) / g) =
      2 * ((r * sm * g) * (1 / (N * g))) / g + 2 * ((r * sm * g) * Real.sqrt (σ * B' ^ 2)) / g +
        2 * (2 * (1 / g) * ℓ / (3 * N)) / g + 2 * (4 * (1 / (N * g))) / g := by
    field_simp
  rw [hsplit]
  linarith only [t1, hT2, hr2, t3a, t3b, t3c, t3d, hplan, hr, hε]

end StatisticalRL.RobustRL.DRVI

namespace StatisticalRL.RobustRL.DRVI

/-- `L = log(SAN/((1−γ)δ)) ≥ 1/4` on the printed range. -/
theorem tv_L_lower {S A N g δ : ℝ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hN : 1 ≤ N) (hg : 0 < g)
    (hg1 : g ≤ 3 / 4) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 / 4 ≤ Real.log (S * A * N / (g * δ)) := by
  have hx : 4 / 3 ≤ S * A * N / (g * δ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : 1 ≤ S * A * N := by
      have h1 : 1 ≤ S * A := by nlinarith only [hS, hA]
      nlinarith only [h1, hN]
    nlinarith only [this, hg, hg1, hδ, hδ1, mul_pos hg hδ]
  have hx0 : 0 < S * A * N / (g * δ) := by linarith
  have := Real.one_sub_inv_le_log_of_pos hx0
  have hinv : (S * A * N / (g * δ))⁻¹ ≤ 3 / 4 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]; linarith only [hx]
  linarith only [this, hinv]

/-- `ℓ = log(8(N+1)² SA/δ) ≤ 17 L`. -/
theorem tv_ell_le {S A N g δ : ℝ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hN : 1 ≤ N) (hg : 0 < g)
    (hg1 : g ≤ 3 / 4) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log (4 * (2 * (N + 1) ^ 2) * (S * A) / δ) ≤ 17 * Real.log (S * A * N / (g * δ)) := by
  have hL := tv_L_lower hS hA hN hg hg1 hδ hδ1
  set x := S * A * N / (g * δ) with hxdef
  have hx0 : 0 < x := by positivity
  have hxN : N ≤ x := by
    rw [hxdef, le_div_iff₀ (by positivity)]
    have h1 : 1 ≤ S * A := by nlinarith only [hS, hA]
    have h2 : g * δ ≤ 1 := by nlinarith only [hg, hg1, hδ, hδ1]
    nlinarith only [h1, h2, hN, mul_pos hg hδ]
  have hxSA : S * A / δ ≤ x := by
    rw [hxdef, div_le_div_iff₀ hδ (by positivity)]
    have h1 : 1 ≤ S * A := by nlinarith only [hS, hA]
    have h2 : g ≤ N := by linarith
    nlinarith only [h1, h2, hδ, mul_pos (show (0:ℝ) < S * A by linarith) hδ]
  have hx1 : 1 ≤ x := hN.trans hxN
  have hbound : 4 * (2 * (N + 1) ^ 2) * (S * A) / δ ≤ 32 * x ^ 3 := by
    have hN1 : (N + 1) ^ 2 ≤ 4 * N ^ 2 := by nlinarith only [hN]
    have e : 4 * (2 * (N + 1) ^ 2) * (S * A) / δ = 8 * (N + 1) ^ 2 * (S * A / δ) := by ring
    rw [e]
    have hSA0 : 0 ≤ S * A / δ := by positivity
    have h1 : 8 * (N + 1) ^ 2 * (S * A / δ) ≤ 8 * (4 * N ^ 2) * (S * A / δ) := by
      apply mul_le_mul_of_nonneg_right _ hSA0; linarith only [hN1]
    have h2 : N ^ 2 * (S * A / δ) ≤ x ^ 2 * x := by
      apply mul_le_mul (pow_le_pow_left₀ (by linarith) hxN 2) hxSA hSA0 (by positivity)
    nlinarith only [h1, h2]
  have hpos : 0 < 4 * (2 * (N + 1) ^ 2) * (S * A) / δ := by positivity
  have hlog : Real.log (4 * (2 * (N + 1) ^ 2) * (S * A) / δ) ≤ Real.log 32 + 3 * Real.log x := by
    calc _ ≤ Real.log (32 * x ^ 3) := Real.log_le_log hpos hbound
      _ = Real.log 32 + 3 * Real.log x := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h32 : Real.log 32 ≤ 7 / 2 := by
    have : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; push_cast; ring
    rw [this]
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  linarith only [hlog, h32, hL]

end StatisticalRL.RobustRL.DRVI
