import Formalization.ModelFree.QLearningChiFixedValueFreedman

/-! K=1 deterministic radius conversion and actual
fixed-comparator concentration. Variance caps are derived, not premises. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiRadiusStateMeasurable : MeasurableSpace State := ⊤
local instance qChiRadiusActionMeasurable : MeasurableSpace Action := ⊤

/-- Pure source arithmetic. This bounded scalar helper consumes the already
proved intermediate variance cap, not the source stochastic conclusion. -/
theorem qChi_K_one_radius_le (γ ηbar Var H W L : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ ηbar) (hv : 0 ≤ Var) (hL : 0 ≤ L)
    (hW : W ≤ γ ^ 2 * ηbar * Var) :
    Real.sqrt (8 * max W ((γ ^ 2 * ηbar * Var) / 2) * L) +
        (4 / 3) * (γ * ηbar * H) * L ≤
      γ * Real.sqrt ((8 * ηbar * L) * Var) + (γ / 6) * (8 * ηbar * L) * H := by
  have hσ : 0 ≤ γ ^ 2 * ηbar * Var := mul_nonneg (mul_nonneg (sq_nonneg _) hη) hv
  have hm : max W ((γ ^ 2 * ηbar * Var) / 2) ≤ γ ^ 2 * ηbar * Var :=
    max_le hW (by nlinarith)
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 8)) hL)
  have he : Real.sqrt (8 * (γ ^ 2 * ηbar * Var) * L) =
      γ * Real.sqrt ((8 * ηbar * L) * Var) := by
    rw [show 8 * (γ ^ 2 * ηbar * Var) * L = γ ^ 2 * ((8 * ηbar * L) * Var) by ring,
      Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq_eq_abs, abs_of_nonneg hγ]
  rw [he] at hs
  nlinarith

/-- Fixed value, actual product law, exact source K=1 simplified radius.
Every stochastic input is supplied by the checked moment/history chain. -/
theorem qChiFixedFluctuation_sourceRadius (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T u : ℕ) (hT : 2 ≤ T) (hu : u ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (hspan : ∀ x y, |v x - v y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    1 - ε ≤ (qSamplingLaw M T).real {data |
      |qChiFixedFluctuationSum M v η T u s a data| ≤
        M.discount * Real.sqrt ((8 * qSourceLateCap M.discount c₂ T * Real.log (2 / ε)) *
          (M.transition s a).variance v) +
        (M.discount / 6) * (8 * qSourceLateCap M.discount c₂ T * Real.log (2 / ε)) * M.effectiveHorizon} := by
  let μ := qSamplingLaw M T
  have hp := qChiFixedFluctuation_freedman M v η c₁ c₂ T u hT hu hc₁ hc₂ hs hspan s a 1
    (by omega) ε hε hε1
  have hcap := qChiFixed_historyPredictableVariance_le M v η c₁ c₂ T u hT hu hc₁ hc₂ hs s a
  have hηbar : 0 ≤ qSourceLateCap M.discount c₂ T := by
    unfold qSourceLateCap
    have hgap := sub_pos.mpr M.discount_lt_one
    have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
    positivity
  have hlog : 0 ≤ Real.log (2 / ε) := (Real.log_pos (by
    apply (lt_div_iff₀ hε).2
    linarith)).le
  have hsub :
      {data | |qChiFixedFluctuationSum M v η T u s a data| ≤ Real.sqrt (8 * max
        (historyPredictableVariance μ (qChiFixedFluctuationIncrement M v η T u s a) T data)
        (qChiFixedVarianceBudget M v c₂ T s a / (2:ℝ)^1) * Real.log (2*1/ε)) +
        (4/3)*(M.discount*qSourceLateCap M.discount c₂ T*M.effectiveHorizon)*Real.log (2*1/ε)} ≤ᵐ[μ]
      {data | |qChiFixedFluctuationSum M v η T u s a data| ≤
        M.discount * Real.sqrt ((8*qSourceLateCap M.discount c₂ T*Real.log (2/ε))*
          (M.transition s a).variance v) +
        (M.discount/6)*(8*qSourceLateCap M.discount c₂ T*Real.log (2/ε))*M.effectiveHorizon} := by
    filter_upwards [hcap] with data hd
    intro hg
    have hr := qChi_K_one_radius_le M.discount (qSourceLateCap M.discount c₂ T)
      ((M.transition s a).variance v) M.effectiveHorizon
      (historyPredictableVariance μ (qChiFixedFluctuationIncrement M v η T u s a) T data)
      (Real.log (2/ε)) M.discount_nonneg hηbar ((M.transition s a).variance_nonneg v) hlog
      (by simpa [qChiFixedVarianceBudget, qRowVariance_eq_distribution, μ] using hd)
    apply hg.trans
    simpa only [pow_one, mul_one, qChiFixedVarianceBudget, qRowVariance_eq_distribution] using hr
  norm_num only [Nat.cast_one] at hp hsub
  exact hp.trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub))

end StatisticalRL.QLearning
