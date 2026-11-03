import Formalization.ModelFree.QLearningChiResidual

/-! Source-domain positivity and exact deterministic
substitution. No sample accuracy or fluctuation probability claim. -/
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The exact source late-rate envelope is strictly positive on its domain. -/
theorem qChiSourceRateEnvelope_pos (γ c₂ : ℝ) (T : ℕ)
    (hγ : γ < 1) (hc₂ : 0 < c₂) (hT : 2 ≤ T) :
    0 < qChiSourceRateEnvelope γ c₂ T := by
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  unfold qChiSourceRateEnvelope
  apply lt_min (by norm_num)
  exact div_pos (by positivity) (by positivity)

/-- No confidence logarithm is silently positive outside its source domain. -/
theorem qChiSourceRadius_pos (ηbar δ : ℝ) (S A T : ℕ)
    (hη : 0 < ηbar) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T) :
    0 < qChiSourceRadius ηbar δ S A T := by
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hSA : (1 : ℝ) ≤ (S : ℝ) * A := by nlinarith
  have hSAT : (2 : ℝ) ≤ (S : ℝ) * A * T := by nlinarith
  have hratio : (1 : ℝ) < 4 * (S : ℝ) * A * T / δ := by
    apply (lt_div_iff₀ hδ).2
    nlinarith
  unfold qChiSourceRadius
  exact mul_pos (mul_pos (by norm_num) hη) (Real.log_pos hratio)

/-- The exact printed reward shift equals the residual helper's expression. -/
theorem qChiSourceRewardShift_eq (M : DiscountedMDP State Action) (ρ : ℝ) :
    qChiSourceRewardShift M.discount ρ = 2 * ρ * M.effectiveHorizon := by
  unfold qChiSourceRewardShift DiscountedMDP.effectiveHorizon
  ring

/-- Actual source substitution for the upper residual; positivity follows
from the source domains rather than an extra rho hypothesis. -/
theorem qChi_upperResidual_source_parameters (M : DiscountedMDP State Action)
    (c₂ δ : ℝ) (T : ℕ) (hc₂ : 0 < c₂) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (Q : State → Action → ℝ)
    (hQ : qRobustBellmanPlus M
      (qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
        (Fintype.card State) (Fintype.card Action) T)
      (qChiSourceRewardShift M.discount
        (qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
          (Fintype.card State) (Fintype.card Action) T)) Q = Q)
    (hspan : ∀ x y, |qLearningValue M Q x - qLearningValue M Q y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T
    M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Q)) +
      (2 - M.discount) * ρ * M.effectiveHorizon ≤ qComparatorResidualPlus M Q s a := by
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  have hρ := qChiSourceRadius_pos _ δ (Fintype.card State) (Fintype.card Action) T
    (qChiSourceRateEnvelope_pos M.discount c₂ T M.discount_lt_one hc₂ hT) hδ hδ1
    (Fintype.card_pos_iff.mpr M.state_nonempty) (Fintype.card_pos_iff.mpr M.action_nonempty) hT
  rw [qChiSourceRewardShift_eq] at hQ
  exact (qChi_upperResidual_bounds M _ hρ.le Q hQ hspan s a).1

/-- Actual source substitution for the lower residual; positivity follows
from the source domains rather than an extra rho hypothesis. -/
theorem qChi_lowerResidual_source_parameters (M : DiscountedMDP State Action)
    (c₂ δ : ℝ) (T : ℕ) (hc₂ : 0 < c₂) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (Q : State → Action → ℝ)
    (hQ : qRobustBellmanMinus M
      (qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
        (Fintype.card State) (Fintype.card Action) T)
      (qChiSourceRewardShift M.discount
        (qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
          (Fintype.card State) (Fintype.card Action) T)) Q = Q)
    (hspan : ∀ x y, |qLearningValue M Q x - qLearningValue M Q y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T
    M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Q)) +
      (2 - M.discount) * ρ * M.effectiveHorizon ≤ qComparatorResidualMinus M Q s a := by
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  have hρ := qChiSourceRadius_pos _ δ (Fintype.card State) (Fintype.card Action) T
    (qChiSourceRateEnvelope_pos M.discount c₂ T M.discount_lt_one hc₂ hT) hδ hδ1
    (Fintype.card_pos_iff.mpr M.state_nonempty) (Fintype.card_pos_iff.mpr M.action_nonempty) hT
  rw [qChiSourceRewardShift_eq] at hQ
  exact (qChi_lowerResidual_bounds M _ hρ.le Q hQ hspan s a).1

/-- The source envelope really is capped at one. -/
theorem qChiSourceRateEnvelope_le_one (γ c₂ : ℝ) (T : ℕ) :
    qChiSourceRateEnvelope γ c₂ T ≤ 1 := min_le_left _ _

/-- The printed reward shift is positive on the actual source domain. -/
theorem qChiSourceRewardShift_pos (γ ρ : ℝ) (hγ : γ < 1) (hρ : 0 < ρ) :
    0 < qChiSourceRewardShift γ ρ := by
  unfold qChiSourceRewardShift
  exact div_pos (mul_pos (by norm_num) hρ) (sub_pos.mpr hγ)

/-- Complete deterministic source-parameter consumption by actual constructed
comparators. Neither their fixed-point equation nor their range is assumed.
The existential proof argument only certifies the derived radius domain. -/
theorem qChi_actualComparatorResidual_source_parameters (M : DiscountedMDP State Action)
    (c₂ δ : ℝ) (T : ℕ) (hc₂ : 0 < c₂) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (s : State) (a : Action) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T
    let b := qChiSourceRewardShift M.discount ρ
    ∃ hρ : 0 ≤ ρ,
      (M.discount * Real.sqrt (ρ * (M.transition s a).variance
          (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))) +
        (2 - M.discount) * ρ * M.effectiveHorizon ≤
          qComparatorResidualPlus M (qRobustPlusFixedPoint M ρ b hρ) s a) ∧
      (M.discount * Real.sqrt (ρ * (M.transition s a).variance
          (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))) +
        (2 - M.discount) * ρ * M.effectiveHorizon ≤
          qComparatorResidualMinus M (qRobustMinusFixedPoint M ρ b hρ) s a) := by
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
    (Fintype.card State) (Fintype.card Action) T
  have hρpos : 0 < ρ := qChiSourceRadius_pos _ δ _ _ T
    (qChiSourceRateEnvelope_pos M.discount c₂ T M.discount_lt_one hc₂ hT) hδ hδ1
    (Fintype.card_pos_iff.mpr M.state_nonempty) (Fintype.card_pos_iff.mpr M.action_nonempty) hT
  refine ⟨hρpos.le, ?_⟩
  simpa only [qChiSourceRewardShift_eq] using
    qChi_actualComparatorResidual_lower M ρ hρpos.le s a

end StatisticalRL.QLearning
