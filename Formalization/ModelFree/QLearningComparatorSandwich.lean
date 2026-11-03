import Formalization.ModelFree.QLearningComparatorUnroll

/-! upper pathwise comparator propagation by exact
warm-start unroll and radius convolution. Statistical and stability layers are
separate; the bounded generic helper exposes its intermediate initial bounds. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def qComparatorRadiusProduct (γ : ℝ) (η : ℕ → ℝ) (L t : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (L+1) t, (1 - η i * (1 - γ))

/-- One-sided action maxima preserve the same additive comparison radius. -/
theorem qComparator_value_upper (M : DiscountedMDP State Action)
    (P Q : State → Action → ℝ) (C : ℝ) (h : ∀ s a, P s a - Q s a ≤ C) (s : State) :
    qLearningValue M P s - qLearningValue M Q s ≤ C := by
  letI : Nonempty Action := M.action_nonempty
  have hh : qLearningValue M P s ≤ qLearningValue M Q s + C := by
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro a ha
    have hp := h s a
    have hq := le_actionMaximum (Q s) a
    change Q s a ≤ qLearningValue M Q s at hq
    linarith
  linarith

/-- Bounded propagation helper. Initial error-plus-residual and absorption
are intermediate source obligations, not a claimed unconditional theorem. -/
theorem qComparator_plus_propagation (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ Q : State → Action → ℝ)
    (L T : ℕ) (_hLT : L ≤ T) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (hinit : ∀ s a, qLearningIterate M η samples Q₀ L s a - Q s a +
      qComparatorResidualPlus M Q s a ≤ C₀)
    (hres : ∀ s a, 0 ≤ qComparatorResidualPlus M Q s a)
    (hnoise : ∀ t, L < t → t ≤ T → ∀ s a,
      |qComparatorPathFluctuation M η samples Q L t s a| ≤ qComparatorResidualPlus M Q s a) :
    ∀ t, L ≤ t → t ≤ T → ∀ s a,
      qLearningIterate M η samples Q₀ t s a - Q s a ≤
        C₀ * qComparatorRadiusProduct M.discount η L t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro hLt htT s a
    by_cases he : L = t
    · subst t
      simp only [qComparatorRadiusProduct, Finset.Icc_eq_empty_of_lt (by omega : L < L+1),
        Finset.prod_empty, mul_one]
      linarith [hinit s a, hres s a]
    have hLt' : L < t := by omega
    let C := ∏ j ∈ Finset.Icc (L+1) t, (1 - η j)
    let R := qComparatorResidualPlus M Q s a
    have hC : 0 ≤ C := by
      apply Finset.prod_nonneg
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact sub_nonneg.mpr (hη i (by omega) (hi'.2.trans htT)).2
    have hun := qComparator_plus_unroll M η samples Q₀ Q L t hLt s a
    have habs := qComparator_absorption_algebra
      (qComparatorPathFluctuation M η samples Q L t s a) R C (hnoise t hLt' htT s a)
    have hstart := mul_le_mul_of_nonneg_left (hinit s a) hC
    have hsum : (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a) -
          qLearningValue M Q (samples i s a))) ≤
        ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
          (C₀ * qComparatorRadiusProduct M.discount η L (i-1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hprev := ih (i-1) (by omega) (by omega) (by omega)
      have hv := qComparator_value_upper M (qLearningIterate M η samples Q₀ (i-1)) Q
        (C₀ * qComparatorRadiusProduct M.discount η L (i-1)) hprev (samples i s a)
      exact mul_le_mul_of_nonneg_left hv (qPositiveWeight_nonneg η t i (by omega) hi'.2
        (fun k hk hkt ↦ hη k hk (hkt.trans htT)))
    have hgsum := mul_le_mul_of_nonneg_left hsum M.discount_nonneg
    have hfactor : (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (C₀ * qComparatorRadiusProduct M.discount η L (i-1))) =
        C₀ * ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
          qComparatorRadiusProduct M.discount η L (i-1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hconv := qComparatorRadius_convolution M.discount η L t hLt
    change C + M.discount * (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
      qComparatorRadiusProduct M.discount η L (i-1)) = qComparatorRadiusProduct M.discount η L t at hconv
    rw [hfactor] at hgsum
    dsimp [C, R] at habs hstart
    nlinarith [hun, habs, hstart, hgsum, hconv]

/-- Bounded propagation helper. Initial error-plus-residual and absorption
are intermediate source obligations, not a claimed unconditional theorem. -/
theorem qComparator_minus_propagation (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ Q : State → Action → ℝ)
    (L T : ℕ) (_hLT : L ≤ T) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (hinit : ∀ s a, Q s a - qLearningIterate M η samples Q₀ L s a +
      qComparatorResidualMinus M Q s a ≤ C₀)
    (hres : ∀ s a, 0 ≤ qComparatorResidualMinus M Q s a)
    (hnoise : ∀ t, L < t → t ≤ T → ∀ s a,
      |qComparatorPathFluctuation M η samples Q L t s a| ≤ qComparatorResidualMinus M Q s a) :
    ∀ t, L ≤ t → t ≤ T → ∀ s a,
      Q s a - qLearningIterate M η samples Q₀ t s a ≤
        C₀ * qComparatorRadiusProduct M.discount η L t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro hLt htT s a
    by_cases he : L = t
    · subst t
      simp only [qComparatorRadiusProduct, Finset.Icc_eq_empty_of_lt (by omega : L < L+1),
        Finset.prod_empty, mul_one]
      linarith [hinit s a, hres s a]
    have hLt' : L < t := by omega
    let C := ∏ j ∈ Finset.Icc (L+1) t, (1 - η j)
    let R := qComparatorResidualMinus M Q s a
    have hC : 0 ≤ C := by
      apply Finset.prod_nonneg
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact sub_nonneg.mpr (hη i (by omega) (hi'.2.trans htT)).2
    have hun := qComparator_minus_unroll M η samples Q₀ Q L t hLt s a
    have habs := qComparator_absorption_algebra
      (-(qComparatorPathFluctuation M η samples Q L t s a)) R C
      (by simpa only [abs_neg] using hnoise t hLt' htT s a)
    have hstart := mul_le_mul_of_nonneg_left (hinit s a) hC
    have hsum : (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (qLearningValue M Q (samples i s a) -
          qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a))) ≤
        ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
          (C₀ * qComparatorRadiusProduct M.discount η L (i-1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hprev := ih (i-1) (by omega) (by omega) (by omega)
      have hv := qComparator_value_upper M Q (qLearningIterate M η samples Q₀ (i-1))
        (C₀ * qComparatorRadiusProduct M.discount η L (i-1)) hprev (samples i s a)
      exact mul_le_mul_of_nonneg_left hv (qPositiveWeight_nonneg η t i (by omega) hi'.2
        (fun k hk hkt ↦ hη k hk (hkt.trans htT)))
    have hgsum := mul_le_mul_of_nonneg_left hsum M.discount_nonneg
    have hfactor : (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (C₀ * qComparatorRadiusProduct M.discount η L (i-1))) =
        C₀ * ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
          qComparatorRadiusProduct M.discount η L (i-1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hconv := qComparatorRadius_convolution M.discount η L t hLt
    change C + M.discount * (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
      qComparatorRadiusProduct M.discount η L (i-1)) = qComparatorRadiusProduct M.discount η L t at hconv
    rw [hfactor] at hgsum
    dsimp [C, R] at habs hstart
    nlinarith [hun, habs, hstart, hgsum, hconv]

/-- Both exact source warm-start constants follow from actual iterate range,
shifted comparator range and residual upper, not assumed error estimates. -/
theorem qComparator_actual_initial_bounds (M : DiscountedMDP State Action) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) (L : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ L → 0 ≤ η i ∧ η i ≤ 1) (s : State) (a : Action) :
    (qLearningIterate M η samples Q₀ L s a - qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a +
        qComparatorResidualPlus M (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a ≤
      (1 + 2*ρ + Real.sqrt ρ) * M.effectiveHorizon) ∧
    (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a - qLearningIterate M η samples Q₀ L s a +
        qComparatorResidualMinus M (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a ≤
      (1 + 2*ρ + Real.sqrt ρ) * M.effectiveHorizon) := by
  have hiter := qLearningIterate_bounds M η samples Q₀ h₀ L hη s a
  have hrange := qRobustComparator_shifted_range M ρ (2*ρ*M.effectiveHorizon) hρ
  have hupper := qChi_actualComparatorResidual_upper M ρ hρ s a
  have hshift : 0 ≤ (2*ρ*M.effectiveHorizon) / (1 - M.discount) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ) M.effectiveHorizon_nonneg)
      (sub_pos.mpr M.discount_lt_one).le
  have hp := (hrange.1 s a).1
  have hm := (hrange.2 s a).2
  exact ⟨by nlinarith [hupper.1], by nlinarith [hupper.2]⟩

/-- Pathwise actual-comparator sandwich on the common absorption condition.
Initial estimates and residual nonnegativity are proved, not supplied as
extra initial-error or target-bound hypotheses. -/
theorem qComparator_actual_sandwich (M : DiscountedMDP State Action) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (L T : ℕ) (hLT : L ≤ T)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1)
    (hplus : ∀ t, L < t → t ≤ T → ∀ s a,
      |qComparatorPathFluctuation M η samples (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) L t s a| ≤
        qComparatorResidualPlus M (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a)
    (hminus : ∀ t, L < t → t ≤ T → ∀ s a,
      |qComparatorPathFluctuation M η samples (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) L t s a| ≤
        qComparatorResidualMinus M (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a) :
    ∀ t, L ≤ t → t ≤ T → ∀ s a,
      (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        ((1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon)*qComparatorRadiusProduct M.discount η L t ≤
          qLearningIterate M η samples Q₀ t s a) ∧
      (qLearningIterate M η samples Q₀ t s a ≤
        qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a +
          ((1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon)*qComparatorRadiusProduct M.discount η L t) := by
  let C₀ := (1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by positivity) M.effectiveHorizon_nonneg
  have hinit := qComparator_actual_initial_bounds M ρ hρ η samples Q₀ h₀ L
    (fun i hi hiL ↦ hη i hi (hiL.trans hLT))
  have hres (s : State) (a : Action) :
      0 ≤ qComparatorResidualPlus M (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a ∧
      0 ≤ qComparatorResidualMinus M (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ) s a := by
    have hl := qChi_actualComparatorResidual_lower M ρ hρ s a
    have hγ := M.discount_nonneg
    have hH := M.effectiveHorizon_nonneg
    have htwo : 0 ≤ 2 - M.discount := by linarith [M.discount_lt_one]
    constructor
    · exact (by positivity : 0 ≤ M.discount * Real.sqrt (ρ * (M.transition s a).variance
        (qLearningValue M (qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ))) +
        (2-M.discount)*ρ*M.effectiveHorizon).trans hl.1
    · exact (by positivity : 0 ≤ M.discount * Real.sqrt (ρ * (M.transition s a).variance
        (qLearningValue M (qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ))) +
        (2-M.discount)*ρ*M.effectiveHorizon).trans hl.2
  have hp := qComparator_plus_propagation M η samples Q₀ _ L T hLT C₀ hC₀ hη
    (fun s a ↦ (hinit s a).1) (fun s a ↦ (hres s a).1) hplus
  have hm := qComparator_minus_propagation M η samples Q₀ _ L T hLT C₀ hC₀ hη
    (fun s a ↦ (hinit s a).2) (fun s a ↦ (hres s a).2) hminus
  intro t ht htT s a
  exact ⟨by linarith [hm t ht htT s a], by linarith [hp t ht htT s a]⟩

end StatisticalRL.QLearning
