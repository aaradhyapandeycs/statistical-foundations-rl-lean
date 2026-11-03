import Formalization.ModelFree.QLearningChiResidualUpper
import Formalization.ModelFree.QLearningWeightTelescope

/-! Actual deterministic comparator error recursion
and finite scalar unroll. No probabilistic or stability conclusion is assumed. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual upper-comparator update decomposition at source step t+1. -/
theorem qComparator_plus_oneStep (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ Q : State → Action → ℝ)
    (t : ℕ) (s : State) (a : Action) :
    qLearningIterate M η samples Q₀ (t+1) s a - Q s a =
      (1 - η (t+1)) * (qLearningIterate M η samples Q₀ t s a - Q s a) +
      M.discount * η (t+1) *
        (qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t+1) s a) -
          qLearningValue M Q (samples (t+1) s a)) +
      M.discount * η (t+1) * (qLearningValue M Q (samples (t+1) s a) -
        (M.transition s a).expectation (qLearningValue M Q)) -
      η (t+1) * qComparatorResidualPlus M Q s a := by
  simp only [qLearningIterate, qComparatorResidualPlus]
  ring

/-- Actual lower-comparator update with the correct negative fluctuation. -/
theorem qComparator_minus_oneStep (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ Q : State → Action → ℝ)
    (t : ℕ) (s : State) (a : Action) :
    Q s a - qLearningIterate M η samples Q₀ (t+1) s a =
      (1 - η (t+1)) * (Q s a - qLearningIterate M η samples Q₀ t s a) +
      M.discount * η (t+1) *
        (qLearningValue M Q (samples (t+1) s a) -
          qLearningValue M (qLearningIterate M η samples Q₀ t) (samples (t+1) s a)) -
      M.discount * η (t+1) * (qLearningValue M Q (samples (t+1) s a) -
        (M.transition s a).expectation (qLearningValue M Q)) -
      η (t+1) * qComparatorResidualMinus M Q s a := by
  simp only [qLearningIterate, qComparatorResidualMinus]
  ring

/-- Generic exact finite recurrence telescope, with a freely chosen warm start.
Its recursion premise is a bounded algebraic helper input, instantiated by the
actual one-step identities above in source consumption. -/
theorem qScalarRecurrence_unroll (η x f : ℕ → ℝ) (L t : ℕ) (hLt : L ≤ t)
    (hx : ∀ i, L < i → i ≤ t → x i = (1 - η i) * x (i-1) + η i * f i) :
    x t = (∏ j ∈ Finset.Icc (L+1) t, (1 - η j)) * x L +
      ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i * f i := by
  induction t with
  | zero =>
    have hL : L = 0 := by omega
    subst L
    simp
  | succ t ih =>
    by_cases hLt' : L ≤ t
    · have hprev := ih hLt' (fun i hi hit ↦ hx i hi (by omega))
      have hstep := hx (t+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hstep
      rw [hstep, hprev, Finset.prod_Icc_succ_top (by omega : L+1 ≤ t+1),
        Finset.sum_Icc_succ_top (by omega : L+1 ≤ t+1)]
      have hw : (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η (t+1) i * f i) =
          (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i * f i) * (1 - η (t+1)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := (Finset.mem_Icc.mp hi).2
        unfold qPositiveWeight
        rw [Finset.prod_Icc_succ_top (by omega : i+1 ≤ t+1)]
        ring
      rw [hw]
      simp only [qPositiveWeight, Finset.Icc_eq_empty_of_lt (by omega : t+1 < t+1+1),
        Finset.prod_empty, mul_one]
      ring
    · have hL : L = t+1 := by omega
      subst L
      simp

/-- The source comparison radius solves exactly the weighted convolution
appearing after deterministic max-value comparison. No rate premise is needed
for the identity; nonnegative rates enter the subsequent inequality induction. -/
theorem qComparatorRadius_convolution (γ : ℝ) (η : ℕ → ℝ) (L t : ℕ) (hLt : L ≤ t) :
    (∏ j ∈ Finset.Icc (L+1) t, (1 - η j)) +
      γ * (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (∏ j ∈ Finset.Icc (L+1) (i-1), (1 - η j * (1 - γ)))) =
      ∏ j ∈ Finset.Icc (L+1) t, (1 - η j * (1 - γ)) := by
  let R : ℕ → ℝ := fun u ↦ ∏ j ∈ Finset.Icc (L+1) u, (1 - η j * (1 - γ))
  have hr (k : ℕ) (hk : L ≤ k) : R (k+1) = (1 - η (k+1)) * R k + η (k+1) * (γ * R k) := by
    dsimp [R]
    rw [Finset.prod_Icc_succ_top (by omega : L+1 ≤ k+1)]
    ring
  have hx : ∀ i, L < i → i ≤ t → R i = (1 - η i) * R (i-1) + η i * (γ * R (i-1)) := by
    intro i hi hit
    have he : i-1+1 = i := by omega
    simpa only [he] using hr (i-1) (by omega)
  have hu := qScalarRecurrence_unroll η R (fun i ↦ γ * R (i-1)) L t hLt hx
  have hRL : R L = 1 := by simp [R]
  rw [hRL, mul_one] at hu
  rw [Finset.mul_sum]
  have hs : (∑ i ∈ Finset.Icc (L+1) t, γ * (qPositiveWeight η t i * R (i-1))) =
      ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i * (γ * R (i-1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change _ = R t
  rw [hs]
  exact hu.symm

/-- Exact scalar residual absorption after unrolling; the initial product
multiplier is retained rather than discarding the residual term. -/
theorem qComparator_absorption_algebra (ξ R C : ℝ) (hξ : |ξ| ≤ R) :
    ξ - (1 - C) * R ≤ C * R := by
  have hh := (le_abs_self ξ).trans hξ
  nlinarith

end StatisticalRL.QLearning
