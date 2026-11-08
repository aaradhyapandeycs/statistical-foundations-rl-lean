import Formalization.ModelFree.AsyncQ.Freedman
import Formalization.ModelFree.AsyncQ.Epoch

/-! # Pathwise propagation on the good events (plan §3.6)

On a path where (i) every epoch window contains enough visits of every pair, so that
`(1-η)^{visits} ≤ θ`, and (ii) all predictable-weight fluctuations are within the Freedman radius,
the errors `Q_T - Q⁺` and `Q⁻ - Q_T` are bounded by the epoch recursion `B_{K}`. -/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.AsyncQ

open StatisticalRL.FiniteMarkov StatisticalRL.QLearning

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

theorem cnt_le (v : ℕ → Prop) [DecidablePred v] (k : ℕ) : cnt v k ≤ k := by
  unfold cnt; exact (card_filter_le _ _).trans (by simp)

/-- Residual facts for the robust comparators at radius `ρ ≤ 1/16`. -/
theorem comparator_facts (M : DiscountedMDP S A) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ16 : ρ ≤ 1 / 16) :
    let Qp := qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
    let Qm := qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
    (∀ s a, 0 ≤ Qp s a) ∧ (∀ s a, Qm s a ≤ M.effectiveHorizon) ∧
    (∀ s₁ s₂, |qLearningValue M Qp s₁ - qLearningValue M Qp s₂| ≤ M.effectiveHorizon) ∧
    (∀ s₁ s₂, |qLearningValue M Qm s₁ - qLearningValue M Qm s₂| ≤ M.effectiveHorizon) ∧
    (∀ s a, M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Qp)) +
        M.discount * ρ * M.effectiveHorizon / 6 ≤ qComparatorResidualPlus M Qp s a ∧
      qComparatorResidualPlus M Qp s a ≤ M.effectiveHorizon) ∧
    (∀ s a, M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Qm)) +
        M.discount * ρ * M.effectiveHorizon / 6 ≤ qComparatorResidualMinus M Qm s a ∧
      qComparatorResidualMinus M Qm s a ≤ M.effectiveHorizon) := by
  intro Qp Qm
  set H := M.effectiveHorizon
  set γ := M.discount
  have hH := M.effectiveHorizon_nonneg
  have hγ := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hshift : 0 ≤ 2 * ρ * H / (1 - γ) := div_nonneg (by positivity) (by linarith)
  have hrange := qRobustComparator_shifted_range M ρ (2 * ρ * H) hρ
  have hspan := qRobustComparator_value_pairwise_span M ρ (2 * ρ * H) hρ
  have hsq : Real.sqrt ρ ≤ 1 / 4 := by
    rw [show (1 / 4 : ℝ) = Real.sqrt ((1 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hres : ∀ (v : S → ℝ), (∀ s₁ s₂, |v s₁ - v s₂| ≤ H) → ∀ s a,
      γ * Real.sqrt (ρ * (M.transition s a).variance v) ≤ H / 4 := fun v hv s a ↦ by
    have hc := qChi_abs_centered_le_of_pairwise (M.transition s a) v H hv
    have hvar := qChi_variance_le_centered_span_sq (M.transition s a) v H hH hc
    have h1 : Real.sqrt (ρ * (M.transition s a).variance v) ≤ Real.sqrt ρ * H := by
      rw [Real.sqrt_mul hρ]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      rw [show H = Real.sqrt (H ^ 2) by rw [Real.sqrt_sq hH]]
      exact Real.sqrt_le_sqrt hvar
    have h2 : Real.sqrt ρ * H ≤ H / 4 := by nlinarith [Real.sqrt_nonneg ρ]
    have h3 : γ * Real.sqrt (ρ * (M.transition s a).variance v) ≤
        Real.sqrt (ρ * (M.transition s a).variance v) := by
      have := Real.sqrt_nonneg (ρ * (M.transition s a).variance v)
      nlinarith
    linarith
  refine ⟨fun s a ↦ by linarith [(hrange.1 s a).1], fun s a ↦ by linarith [(hrange.2 s a).2],
    fun s₁ s₂ ↦ (hspan s₁ s₂).1, fun s₁ s₂ ↦ (hspan s₁ s₂).2, fun s a ↦ ?_, fun s a ↦ ?_⟩
  · have hb := qChi_upperResidual_bounds M ρ hρ Qp
      (qRobustPlusFixedPoint_spec M ρ (2 * ρ * H) hρ) (fun x y ↦ (hspan x y).1) s a
    have := hres _ (fun x y ↦ (hspan x y).1) s a
    have hρH : 0 ≤ ρ * H := mul_nonneg hρ hH
    constructor
    · nlinarith
    · nlinarith
  · have hb := qChi_lowerResidual_bounds M ρ hρ Qm
      (qRobustMinusFixedPoint_spec M ρ (2 * ρ * H) hρ) (fun x y ↦ (hspan x y).2) s a
    have := hres _ (fun x y ↦ (hspan x y).2) s a
    have hρH : 0 ≤ ρ * H := mul_nonneg hρ hH
    constructor
    · nlinarith
    · nlinarith

theorem path_bound (M : DiscountedMDP S A) {η ρ θ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hρ : 0 ≤ ρ)
    (hρ16 : ρ ≤ 1 / 16) (hθ0 : 0 ≤ θ) (Q₀ : S → A → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) {T : ℕ} (x : Fin (T + 1) → S × A)
    (Kep ℓ : ℕ) (hKℓ : Kep * ℓ ≤ T)
    (hvis : ∀ z, ∀ k < Kep, ∀ K', ℓ ≤ K' → (1 - η) ^ cnt (visits x (k * ℓ) z) K' ≤ θ)
    (hflp : ∀ z : S × A, ∀ k < Kep, ∀ m n, m ≤ T → n ≤ T → k * ℓ + m ≤ T →
      |∑ j ∈ range m, weight (visits x (k * ℓ) z) η n j * noise M x (k * ℓ) z
        (qLearningValue M (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ)) j| ≤
        M.discount * Real.sqrt (ρ * (M.transition z.1 z.2).variance
          (qLearningValue M (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ))) +
        M.discount * ρ * M.effectiveHorizon / 6)
    (hflm : ∀ z : S × A, ∀ k < Kep, ∀ m n, m ≤ T → n ≤ T → k * ℓ + m ≤ T →
      |∑ j ∈ range m, weight (visits x (k * ℓ) z) η n j * noise M x (k * ℓ) z
        (qLearningValue M (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ)) j| ≤
        M.discount * Real.sqrt (ρ * (M.transition z.1 z.2).variance
          (qLearningValue M (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ))) +
        M.discount * ρ * M.effectiveHorizon / 6) :
    ∀ s a, iterate M η Q₀ x T s a - qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ s a ≤
        epochBound M.discount θ M.effectiveHorizon M.effectiveHorizon Kep ∧
      qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ s a - iterate M η Q₀ x T s a ≤
        epochBound M.discount θ M.effectiveHorizon M.effectiveHorizon Kep := by
  obtain ⟨hQp0, hQmh, -, -, hresp, hresm⟩ := comparator_facts M hρ hρ16
  set Qp := qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
  set Qm := qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
  have hQ := iterate_mem M hη0.le hη1 h₀ x
  have hH := M.effectiveHorizon_nonneg
  have hγ := M.discount_nonneg
  have hplus := epoch_induction (Z := S × A) (fun t z ↦ iterate M η Q₀ x t z.1 z.2 - Qp z.1 z.2)
    (fun z ↦ qComparatorResidualPlus M Qp z.1 z.2) hγ hθ0 hH hH Kep ℓ T
    (fun t _ z ↦ by have := (hQ t z.1 z.2).2; have := hQp0 z.1 z.2; linarith)
    (fun k hk t ht htT B hB z ↦ by
      obtain ⟨τ, hτ⟩ : ∃ τ, τ = k * ℓ := ⟨_, rfl⟩
      rw [← hτ] at hB ⊢
      have ht' : τ + ℓ ≤ t := by rw [hτ, ← Nat.succ_mul]; exact ht
      have hw := window_plus_le M Q₀ hη0.le hη1 x Qp τ (t - τ) z.1 z.2 (B := B)
        (fun t' h1 h2 s' a' ↦ hB t' h1 (by omega) (s', a'))
      rw [show τ + (t - τ) = t by omega] at hw
      refine ⟨(1 - η) ^ cnt (visits x τ (z.1, z.2)) (t - τ),
        accum (visits x τ (z.1, z.2)) η (noise M x τ (z.1, z.2) (qLearningValue M Qp)) (t - τ),
        pow_nonneg (by linarith) _, ?_, pow_le_one₀ (by linarith) (by linarith), ?_,
        (hresp _ _).2, hw⟩
      · have := hvis (z.1, z.2) k hk (t - τ) (by omega); rwa [← hτ] at this
      · rw [accum_eq]
        have := hflp (z.1, z.2) k hk (t - τ) (cnt (visits x τ (z.1, z.2)) (t - τ)) (by omega)
          ((cnt_le _ _).trans (by omega)) (by omega)
        rw [← hτ] at this
        exact (le_abs_self _).trans (this.trans (hresp z.1 z.2).1))
  have hminus := epoch_induction (Z := S × A) (fun t z ↦ Qm z.1 z.2 - iterate M η Q₀ x t z.1 z.2)
    (fun z ↦ qComparatorResidualMinus M Qm z.1 z.2) hγ hθ0 hH hH Kep ℓ T
    (fun t _ z ↦ by have := (hQ t z.1 z.2).1; have := hQmh z.1 z.2; linarith)
    (fun k hk t ht htT B hB z ↦ by
      obtain ⟨τ, hτ⟩ : ∃ τ, τ = k * ℓ := ⟨_, rfl⟩
      rw [← hτ] at hB ⊢
      have ht' : τ + ℓ ≤ t := by rw [hτ, ← Nat.succ_mul]; exact ht
      have hw := window_minus_le M Q₀ hη0.le hη1 x Qm τ (t - τ) z.1 z.2 (B := B)
        (fun t' h1 h2 s' a' ↦ hB t' h1 (by omega) (s', a'))
      rw [show τ + (t - τ) = t by omega, accum_neg] at hw
      refine ⟨(1 - η) ^ cnt (visits x τ (z.1, z.2)) (t - τ),
        -accum (visits x τ (z.1, z.2)) η (noise M x τ (z.1, z.2) (qLearningValue M Qm)) (t - τ),
        pow_nonneg (by linarith) _, ?_, pow_le_one₀ (by linarith) (by linarith), ?_,
        (hresm _ _).2, hw⟩
      · have := hvis (z.1, z.2) k hk (t - τ) (by omega); rwa [← hτ] at this
      · rw [accum_eq]
        have := hflm (z.1, z.2) k hk (t - τ) (cnt (visits x τ (z.1, z.2)) (t - τ)) (by omega)
          ((cnt_le _ _).trans (by omega)) (by omega)
        rw [← hτ] at this
        exact (neg_le_abs _).trans (this.trans (hresm z.1 z.2).1))
  intro s a
  exact ⟨hplus Kep le_rfl T hKℓ le_rfl (s, a), hminus Kep le_rfl T hKℓ le_rfl (s, a)⟩

end StatisticalRL.AsyncQ
