import Formalization.OfflineRL.MonotoneContractionCorrected

/-!
# Iteration count of offline VI-LCB

Source: `chapters/offlineRL.tex:892`, the prose after `lem:monotone-contraction` (`:872–890`):
`Q̂_τ` is `ε`-accurate for `Q̂⋆_pe` after at most `(1/(1−γ)) log(1/(ε(1−γ)))` iterations.
The fixed point `Q̂⋆_pe` is the one of `Input.lem_monotone_contraction_corrected`, so the result
is restricted to that lemma's domain `1/2 ≤ γ` (`docs/SOURCE-ISSUES.md#C10`); for `γ < 1/2` the
claim is open (neither proved nor refuted).
-/

namespace StatisticalRL.OfflineVILCB

/-- `γ^τ ≤ x` once `τ ≥ log(1/x)/(1−γ)`, for `0 ≤ γ < 1` and `x > 0` (from `γ ≤ e^{γ−1}`). -/
theorem discount_pow_le_of_log_inv_le (γ x : ℝ) (τ : ℕ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hx : 0 < x) (hτ : Real.log (1 / x) / (1 - γ) ≤ τ) : γ ^ τ ≤ x := by
  have hh : 0 < 1 - γ := sub_pos.mpr hγ1
  have hexp : γ ≤ Real.exp (γ - 1) := by
    have := Real.add_one_le_exp (γ - 1)
    linarith
  have hpow : γ ^ τ ≤ Real.exp (γ - 1) ^ τ := pow_le_pow_left₀ hγ hexp τ
  rw [← Real.exp_nat_mul] at hpow
  have hτ' : Real.log (1 / x) ≤ τ * (1 - γ) := (div_le_iff₀ hh).1 hτ
  have harg : (τ : ℝ) * (γ - 1) ≤ Real.log x := by
    rw [one_div, Real.log_inv] at hτ'
    linarith
  calc
    γ ^ τ ≤ Real.exp (τ * (γ - 1)) := hpow
    _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr harg
    _ = x := Real.exp_log hx

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

namespace Input

/-- **Iteration count after Lemma 6.2** (`offlineRL.tex:892`), restricted to the domain
`1/2 ≤ γ` of the corrected Lemma 6.2: the unique fixed point `Q̂⋆_pe` of `T_pess` exists, and every
`τ ≥ log(1/(ε(1−γ)))/(1−γ)` gives `‖Q̂_τ − Q̂⋆_pe‖∞ ≤ ε`. -/
theorem iter_iterationCount_restricted (M : Input S A) (hγ : 1 / 2 ≤ M.γ) :
    ∃ Qstar : S → A → ℝ, M.pess Qstar = Qstar ∧ (∀ Q, M.pess Q = Q → Q = Qstar) ∧
      ∀ ε : ℝ, 0 < ε → ∀ τ : ℕ, Real.log (1 / (ε * (1 - M.γ))) / (1 - M.γ) ≤ τ →
        ‖M.iter τ - Qstar‖ ≤ ε := by
  obtain ⟨Qstar, hfix, huniq, hiter, -⟩ := M.lem_monotone_contraction_corrected hγ
  refine ⟨Qstar, hfix, huniq, fun ε hε τ hτ ↦ ?_⟩
  have hh : 0 < 1 - M.γ := sub_pos.mpr M.γ_lt_one
  have hpow : M.γ ^ τ ≤ ε * (1 - M.γ) :=
    discount_pow_le_of_log_inv_le M.γ (ε * (1 - M.γ)) τ M.γ_nonneg M.γ_lt_one
      (mul_pos hε hh) hτ
  calc ‖M.iter τ - Qstar‖ ≤ M.γ ^ τ / (1 - M.γ) := (hiter τ).2
    _ ≤ ε * (1 - M.γ) / (1 - M.γ) := div_le_div_of_nonneg_right hpow hh.le
    _ = ε := by field_simp

end Input

end StatisticalRL.OfflineVILCB
