import Formalization.RobustRL.LowerBounds.LowerBound75Values

/-!
# Corrected Theorem 7.5: parameters and real-number estimates

With `h = 1-γ`, `s = √σ`, `u = (s + √(σ+4h))/2` (so `u² = s u + h`, `u ≥ s`),
`P = 2u - s + s u²`, `δ = 128 h² ε (1+u²)² / P`, `u' = u + δ`, the nominal leave
probabilities are `ℓ(v) = v²/(1+v²)` and the χ² robust leave probabilities are
`T(v) = v (v - s)/(1+v²)` (`ChiPair σ (ℓ v) (T v)` for `v ≥ s`, `v > 0`).
-/

namespace StatisticalRL.RobustRL.Ch7.LowerBound75

/-- Nominal leave probability `ℓ(v) = v²/(1+v²)`. -/
noncomputable def ellf (v : ℝ) : ℝ := v ^ 2 / (1 + v ^ 2)

/-- χ² robust leave probability `T(v) = v(v-s)/(1+v²)`. -/
noncomputable def tf (s v : ℝ) : ℝ := v * (v - s) / (1 + v ^ 2)

/-- `u = (√σ + √(σ+4h))/2`. -/
noncomputable def uf (σ h : ℝ) : ℝ := (Real.sqrt σ + Real.sqrt (σ + 4 * h)) / 2

/-- `P = 2u - s + s u²`. -/
noncomputable def pf (s u : ℝ) : ℝ := 2 * u - s + s * u ^ 2

/-- `δ = 128 h² ε (1+u²)² / P`. -/
noncomputable def df (s u h ε : ℝ) : ℝ := 128 * h ^ 2 * ε * (1 + u ^ 2) ^ 2 / pf s u

theorem uf_spec {σ h : ℝ} (hσ : 0 ≤ σ) (hh : 0 < h) :
    0 ≤ Real.sqrt σ ∧ Real.sqrt σ ^ 2 = σ ∧ 0 < uf σ h ∧ Real.sqrt σ ≤ uf σ h ∧
      uf σ h ^ 2 = Real.sqrt σ * uf σ h + h := by
  have hs0 := Real.sqrt_nonneg σ
  have hs2 : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ
  have hq2 : Real.sqrt (σ + 4 * h) ^ 2 = σ + 4 * h := Real.sq_sqrt (by linarith)
  have hqs : Real.sqrt σ ≤ Real.sqrt (σ + 4 * h) := Real.sqrt_le_sqrt (by linarith)
  have hq0 : 0 < Real.sqrt (σ + 4 * h) := Real.sqrt_pos.2 (by linarith)
  refine ⟨hs0, hs2, ?_, ?_, ?_⟩
  · unfold uf; linarith
  · unfold uf; linarith
  · unfold uf; nlinarith

theorem chiPair_of {σ s v : ℝ} (hs0 : 0 ≤ s) (hs2 : s ^ 2 = σ) (hv : 0 < v) (hsv : s ≤ v) :
    ChiPair σ (ellf v) (tf s v) := by
  have hd : 0 < 1 + v ^ 2 := by positivity
  refine ⟨by unfold ellf; positivity, ?_, ?_, ?_, ?_⟩
  · unfold ellf; rw [div_lt_one hd]; linarith
  · unfold tf; apply div_nonneg _ hd.le; nlinarith
  · unfold tf ellf; apply div_le_div_of_nonneg_right _ hd.le; nlinarith
  · unfold tf ellf; rw [← hs2]; field_simp; ring

variable {s u h : ℝ}

theorem tf_base (hd : u ^ 2 = s * u + h) : tf s u = h / (1 + u ^ 2) := by
  unfold tf; congr 1; nlinarith

theorem tf_diff (δ : ℝ) :
    tf s (u + δ) - tf s u =
      δ * (pf s u + δ * (1 + s * u)) / ((1 + u ^ 2) * (1 + (u + δ) ^ 2)) := by
  unfold tf pf
  have h1 : (1 + u ^ 2) ≠ 0 := by positivity
  have h2 : (1 + (u + δ) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem ellf_diff (δ : ℝ) :
    ellf (u + δ) - ellf u = δ * (2 * u + δ) / ((1 + u ^ 2) * (1 + (u + δ) ^ 2)) := by
  unfold ellf
  have h1 : (1 + u ^ 2) ≠ 0 := by positivity
  have h2 : (1 + (u + δ) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem ellf_var : ellf u * (1 - ellf u) = u ^ 2 / (1 + u ^ 2) ^ 2 := by
  unfold ellf
  have h1 : (1 + u ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `u P = u⁴ + (1-h)u² + h`. -/
theorem u_pf (hd : u ^ 2 = s * u + h) : u * pf s u = u ^ 4 + (1 - h) * u ^ 2 + h := by
  unfold pf
  have : s * u = u ^ 2 - h := by linarith
  have e : u * (2 * u - s + s * u ^ 2) = 2 * u ^ 2 - s * u + (s * u) * u ^ 2 := by ring
  rw [e, this]; ring

theorem pf_pos (hs0 : 0 ≤ s) (hu : 0 < u) (hsu : s ≤ u) : 0 < pf s u := by
  unfold pf; have : 0 ≤ s * u ^ 2 := by positivity
  linarith

/-- (A5): `h (1+u²)² ≤ 4 u P`. -/
theorem key_delta (hd : u ^ 2 = s * u + h) (hh0 : 0 < h) (hh1 : h ≤ 1 / 4) :
    h * (1 + u ^ 2) ^ 2 ≤ 4 * (u * pf s u) := by
  rw [u_pf hd]
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hu4 : 0 ≤ u ^ 4 := by positivity
  have e : 4 * (u ^ 4 + (1 - h) * u ^ 2 + h) - h * (1 + u ^ 2) ^ 2 =
      (4 - h) * u ^ 4 + (4 - 6 * h) * u ^ 2 + 3 * h := by ring
  have : 0 ≤ (4 - h) * u ^ 4 + (4 - 6 * h) * u ^ 2 + 3 * h := by
    have a1 : 0 ≤ (4 - h) * u ^ 4 := mul_nonneg (by linarith) hu4
    have a2 : 0 ≤ (4 - 6 * h) * u ^ 2 := mul_nonneg (by linarith) hu2
    linarith
  linarith

/-- (A6): `(h + σ)(1+u²)² ≤ 9 P²` (with `σ = s²`). -/
theorem key_test (hu : 0 < u) (hd : u ^ 2 = s * u + h)
    (hh0 : 0 < h) (hh1 : h ≤ 1 / 4) :
    (h + s ^ 2) * (1 + u ^ 2) ^ 2 ≤ 9 * pf s u ^ 2 := by
  have hup := u_pf hd
  have hu2 : 0 < u ^ 2 := by positivity
  -- `u² (h + s²) ≤ (u² + h)²`
  have h1 : u ^ 2 * (h + s ^ 2) ≤ (u ^ 2 + h) ^ 2 := by
    have : u ^ 2 * s ^ 2 = (u ^ 2 - h) ^ 2 := by
      have : s * u = u ^ 2 - h := by linarith
      rw [← this]; ring
    nlinarith
  -- `(u² + h)(1 + u²) ≤ 3 u P`
  have h2 : (u ^ 2 + h) * (1 + u ^ 2) ≤ 3 * (u * pf s u) := by
    rw [hup]
    have : 0 ≤ 2 * (u ^ 2) ^ 2 + 2 * u ^ 2 * (1 - 2 * h) + 2 * h := by
      have := mul_nonneg hu2.le (by linarith : (0 : ℝ) ≤ 1 - 2 * h)
      have := sq_nonneg (u ^ 2)
      linarith
    nlinarith
  have h3 : 0 ≤ (u ^ 2 + h) * (1 + u ^ 2) := by positivity
  have h4 : ((u ^ 2 + h) * (1 + u ^ 2)) ^ 2 ≤ (3 * (u * pf s u)) ^ 2 :=
    pow_le_pow_left₀ h3 h2 2
  have h5 : u ^ 2 * ((h + s ^ 2) * (1 + u ^ 2) ^ 2) ≤ u ^ 2 * (9 * pf s u ^ 2) := by
    have h6 : u ^ 2 * ((h + s ^ 2) * (1 + u ^ 2) ^ 2) ≤ (u ^ 2 + h) ^ 2 * (1 + u ^ 2) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (1 + u ^ 2))
      nlinarith
    nlinarith
  exact le_of_mul_le_mul_left h5 hu2

end StatisticalRL.RobustRL.Ch7.LowerBound75
