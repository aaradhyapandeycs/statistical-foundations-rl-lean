import Formalization.OfflineRL.MonotoneContractionCorrected

/-! Preliminary value and penalty estimates for `lem:offline-prelim`.

Source: `chapters/offlineRL.tex:1078–1094`; parent Theorem 6.3 regime
`:903–928`. -/

namespace StatisticalRL.OfflineVILCB.Input

variable {S A : Type*} [Fintype S] [Fintype A]

theorem bonus_add_constant (M : Input S A) (s : S) (a : A)
    (V : S → ℝ) (c : ℝ) :
    M.bonus s a (fun t => V t + c) = M.bonus s a V := by
  unfold bonus
  rw [StatisticalRL.OfflineVILCB.variance_add_const]

/-- An auxiliary bound on vectors with bounded span; it assumes neither a
sampling-law certificate nor a penalty-difference bound. -/
theorem bonus_abs_sub_le_of_span (M : Input S A) (s : S) (a : A)
    (V W : S → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ t u, V t - V u ≤ 1 / (1 - M.γ))
    (hW : ∀ t u, W t - W u ≤ 1 / (1 - M.γ))
    (hclose : ∀ t, |V t - W t| ≤ ε) :
    |M.bonus s a V - M.bonus s a W| ≤ ε := by
  have side : ∀ (f g : S → ℝ),
      (∀ t u, f t - f u ≤ 1 / (1 - M.γ)) →
      (∀ t u, g t - g u ≤ 1 / (1 - M.γ)) →
      (∀ t, |f t - g t| ≤ ε) →
      M.bonus s a f - M.bonus s a g ≤ ε := by
    intro f g hf hg hfg
    have horder : ∀ t, g t ≤ f t + ε := by
      intro t
      have h := (abs_le.mp (hfg t)).1
      linarith
    have hshift : ∀ t u,
        (f t + ε) - (f u + ε) ≤ 1 / (1 - M.γ) := by
      intro t u
      linarith [hf t u]
    have hb := M.bonus_sub_le s a g (fun t => f t + ε) horder hg hshift
    rw [M.bonus_add_constant] at hb
    have he : (M.Phat s a).expectation (fun t => f t + ε - g t) ≤ 2 * ε := by
      apply FiniteDistribution.expectation_le_const
      intro t
      have h := (abs_le.mp (hfg t)).2
      linarith
    linarith
  exact abs_sub_le_iff.mpr
    ⟨side V W hV hW hclose,
      side W V hW hV (fun t => by simpa [abs_sub_comm] using hclose t)⟩

variable [Nonempty A]

theorem value_abs_sub_le (Q W : S → A → ℝ) (ε : ℝ)
    (hclose : ∀ s a, |Q s a - W s a| ≤ ε) (s : S) :
    |value Q s - value W s| ≤ ε := by
  have hQ : value Q s ≤ value W s + ε := by
    apply value_le
    intro a
    have h := (abs_le.mp (hclose s a)).2
    linarith [le_value W s a]
  have hW : value W s ≤ value Q s + ε := by
    apply value_le
    intro a
    have h := (abs_le.mp (hclose s a)).1
    linarith [le_value Q s a]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem value_norm_sub_le (Q W : S → A → ℝ) :
    ‖value Q - value W‖ ≤ ‖Q - W‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (Q - W))).mpr
  intro s
  rw [Real.norm_eq_abs]
  exact value_abs_sub_le Q W _ (fun t a => by
    simpa [dist_eq_norm] using abs_le_dist Q W t a) s

/-- The source parent theorem's stopping rule implies Lemma6.2's logarithmic
stopping rule. This is a scalar implication, not an added Q-error premise. -/
theorem source_stopping_threshold (M : Input S A) (hγ : 1 / 2 ≤ M.γ) (τ : ℕ)
    (hτ : (1 / (1 - M.γ)) * Real.log (M.N / (1 - M.γ)) ≤ τ) :
    Real.log (M.N / (1 - M.γ)) / Real.log (1 / M.γ) ≤ τ := by
  have hγpos : 0 < M.γ := by linarith
  have hβ := M.one_sub_γ_pos
  have hlog : 1 - M.γ ≤ Real.log (1 / M.γ) := by
    rw [one_div, Real.log_inv]
    have h := Real.log_le_sub_one_of_pos hγpos
    linarith
  have hden : 0 < Real.log (1 / M.γ) := lt_of_lt_of_le hβ hlog
  apply (div_le_iff₀ hden).mpr
  have hbase : Real.log (M.N / (1 - M.γ)) ≤ (τ : ℝ) * (1 - M.γ) := by
    apply (div_le_iff₀ hβ).mp
    simpa [div_eq_mul_inv, mul_comm] using hτ
  exact hbase.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg τ))

/-- The actual finite-iteration VI-LCB endpoint in the parent theorem's
discount regime. The fixed point and Q-error are produced inside this proof.
The two final bounds are the conclusions of source `lem:offline-prelim`.
The general Input carrier is a disclosed extension to arbitrary counts and
empirical stochastic rows; dataset-realized inputs are included. -/
theorem exists_fixed_point_preliminary_facts (M : Input S A)
    (hγ : 1 / 2 ≤ M.γ) (τ : ℕ)
    (hτ : (1 / (1 - M.γ)) * Real.log (M.N / (1 - M.γ)) ≤ τ) :
    ∃ Qstar : S → A → ℝ,
      M.pess Qstar = Qstar ∧
      (∀ Q, M.pess Q = Q → Q = Qstar) ∧
      ‖value (M.iter τ) - value Qstar‖ ≤ 1 / M.N ∧
      ∀ s a, |M.bonus s a (value Qstar) -
        M.bonus s a (value (M.iter τ))| ≤ 2 / M.N := by
  obtain ⟨Qstar, hfix, huniq, hiter, hstop⟩ :=
    M.lem_monotone_contraction_corrected hγ
  have hQclose := hstop τ (M.source_stopping_threshold hγ τ hτ)
  have hVclose : ‖value (M.iter τ) - value Qstar‖ ≤ 1 / M.N :=
    (value_norm_sub_le (M.iter τ) Qstar).trans hQclose
  refine ⟨Qstar, hfix, huniq, hVclose, ?_⟩
  intro s a
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
  have hnonneg : (0 : ℝ) ≤ 1 / M.N := by positivity
  have hpointwise : ∀ t, |value Qstar t - value (M.iter τ) t| ≤ 1 / M.N := by
    intro t
    have h := (norm_le_pi_norm (value (M.iter τ) - value Qstar) t).trans hVclose
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  have hb := M.bonus_abs_sub_le_of_span s a (value Qstar) (value (M.iter τ))
    (1 / M.N) hnonneg
    (M.value_range Qstar (M.fixed_mem_box Qstar hfix))
    (M.value_range (M.iter τ) (M.iter_mem_box τ)) hpointwise
  exact hb.trans (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hN.le)

end StatisticalRL.OfflineVILCB.Input
