import Mathlib.Tactic

/-! # Deterministic epoch contraction (plan §3.6)

If on every epoch window the unrolled error obeys
`e_t ≤ Pi e_{τ_k} + (1-Pi)(γ B - Res) + F` with `F ≤ Res ≤ R` and `0 ≤ Pi ≤ min(θ,1)`, whenever all
errors on `[τ_k, t)` are at most `B`, then the errors after epoch `k` are bounded by
`B_{k+1} = (γ+θ) B_k + θ R`, and `B_k ≤ (γ+θ)^k B₀ + θ R/(1-γ-θ)`. -/

namespace StatisticalRL.AsyncQ

/-- `B₀`, `B_{k+1} = (γ+θ) B_k + θ R`. -/
noncomputable def epochBound (γ θ R B₀ : ℝ) : ℕ → ℝ
  | 0 => B₀
  | k + 1 => (γ + θ) * epochBound γ θ R B₀ k + θ * R

theorem epochBound_nonneg {γ θ R B₀ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hB₀ : 0 ≤ B₀)
    (k : ℕ) : 0 ≤ epochBound γ θ R B₀ k := by
  induction k with
  | zero => exact hB₀
  | succ k ih => simp only [epochBound]; positivity

theorem epochBound_le {γ θ R B₀ : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hR : 0 ≤ R) (ha : γ + θ < 1)
    (k : ℕ) : epochBound γ θ R B₀ k ≤ (γ + θ) ^ k * B₀ + θ * R / (1 - (γ + θ)) := by
  induction k with
  | zero => simp only [epochBound, pow_zero, one_mul]; have : 0 ≤ θ * R / (1 - (γ + θ)) := by
              apply div_nonneg (mul_nonneg hθ hR); linarith
            linarith
  | succ k ih =>
    simp only [epochBound]
    have h1 := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ γ + θ)
    have h2 : (γ + θ) * (θ * R / (1 - (γ + θ))) + θ * R = θ * R / (1 - (γ + θ)) := by
      have hne : 1 - (γ + θ) ≠ 0 := by linarith
      field_simp
      ring
    rw [pow_succ]
    nlinarith

theorem epoch_induction {Z : Type*} (err : ℕ → Z → ℝ) (Res : Z → ℝ) {γ θ R B₀ : ℝ}
    (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hB₀ : 0 ≤ B₀) (Kep ℓ T : ℕ)
    (hbase : ∀ t ≤ T, ∀ z, err t z ≤ B₀)
    (hwin : ∀ k < Kep, ∀ t, (k + 1) * ℓ ≤ t → t ≤ T → ∀ B : ℝ,
      (∀ t', k * ℓ ≤ t' → t' < t → ∀ z, err t' z ≤ B) → ∀ z, ∃ Pi F : ℝ, 0 ≤ Pi ∧ Pi ≤ θ ∧
        Pi ≤ 1 ∧ F ≤ Res z ∧ Res z ≤ R ∧
        err t z ≤ Pi * err (k * ℓ) z + (1 - Pi) * (γ * B - Res z) + F) :
    ∀ k ≤ Kep, ∀ t, k * ℓ ≤ t → t ≤ T → ∀ z, err t z ≤ epochBound γ θ R B₀ k := by
  intro k
  induction k with
  | zero => intro _ t _ ht z; exact hbase t ht z
  | succ k ih =>
    intro hk t ht htT z
    have hBk := epochBound_nonneg hγ hθ hR hB₀ k (γ := γ)
    obtain ⟨Pi, F, hPi0, hPiθ, hPi1, hF, hRes, he⟩ := hwin k (by omega) t ht htT
      (epochBound γ θ R B₀ k)
      (fun t' h1 h2 z ↦ ih (by omega) t' h1 (by omega) z) z
    have he0 := ih (by omega) (k * ℓ) le_rfl (le_trans (by nlinarith) (ht.trans htT)) z
    simp only [epochBound]
    have h1 : Pi * (err (k * ℓ) z + Res z) ≤ θ * (epochBound γ θ R B₀ k + R) := by
      calc Pi * (err (k * ℓ) z + Res z) ≤ Pi * (epochBound γ θ R B₀ k + R) :=
            mul_le_mul_of_nonneg_left (by linarith) hPi0
        _ ≤ θ * (epochBound γ θ R B₀ k + R) :=
            mul_le_mul_of_nonneg_right hPiθ (by linarith)
    have h2 : (1 - Pi) * (γ * epochBound γ θ R B₀ k) ≤ γ * epochBound γ θ R B₀ k := by
      have : 0 ≤ γ * epochBound γ θ R B₀ k := mul_nonneg hγ hBk
      nlinarith
    nlinarith

end StatisticalRL.AsyncQ
