import Formalization.ModelFree.QLearningComparatorRecursion

/-! exact pathwise finite comparator decomposition.
No statistical event or desired error bound is assumed. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def qComparatorPathFluctuation (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → Action → State)
    (Q : State → Action → ℝ) (L t : ℕ) (s : State) (a : Action) : ℝ :=
  M.discount * ∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
    (qLearningValue M Q (samples i s a) - (M.transition s a).expectation (qLearningValue M Q))

/-- Exact affine finite-sum expansion used for both residual signs. -/
theorem qComparator_weighted_affine_sum (S : Finset ℕ) (w a b : ℕ → ℝ) (γ R : ℝ) :
    (∑ i ∈ S, w i * (γ * a i + γ * b i - R)) =
      γ * (∑ i ∈ S, w i * a i) + γ * (∑ i ∈ S, w i * b i) - (∑ i ∈ S, w i) * R := by
  have he (i : ℕ) : w i * (γ * a i + γ * b i - R) =
      γ * (w i * a i) + γ * (w i * b i) - w i * R := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.sum_mul]

/-- Actual source upper decomposition, valid also at the empty warm-start window. -/
theorem qComparator_plus_unroll (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ Q : State → Action → ℝ)
    (L t : ℕ) (hLt : L ≤ t) (s : State) (a : Action) :
    qLearningIterate M η samples Q₀ t s a - Q s a =
      (∏ j ∈ Finset.Icc (L+1) t, (1 - η j)) * (qLearningIterate M η samples Q₀ L s a - Q s a) +
      M.discount * (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a) -
          qLearningValue M Q (samples i s a))) +
      qComparatorPathFluctuation M η samples Q L t s a -
      (1 - ∏ j ∈ Finset.Icc (L+1) t, (1 - η j)) * qComparatorResidualPlus M Q s a := by
  let x := fun i ↦ qLearningIterate M η samples Q₀ i s a - Q s a
  let f := fun i ↦ M.discount *
      (qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a) -
        qLearningValue M Q (samples i s a)) +
    M.discount * (qLearningValue M Q (samples i s a) -
      (M.transition s a).expectation (qLearningValue M Q)) - qComparatorResidualPlus M Q s a
  have hx : ∀ i, L < i → i ≤ t → x i = (1 - η i) * x (i-1) + η i * f i := by
    intro i hi hit
    have h := qComparator_plus_oneStep M η samples Q₀ Q (i-1) s a
    have he : i-1+1 = i := by omega
    rw [he] at h
    dsimp [x, f]
    nlinarith [h]
  have hu := qScalarRecurrence_unroll η x f L t hLt hx
  have hs := qComparator_weighted_affine_sum (Finset.Icc (L+1) t) (qPositiveWeight η t)
    (fun i ↦ qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a) -
      qLearningValue M Q (samples i s a))
    (fun i ↦ qLearningValue M Q (samples i s a) - (M.transition s a).expectation (qLearningValue M Q))
    M.discount (qComparatorResidualPlus M Q s a)
  change (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i * f i) = _ at hs
  rw [hs, qPositiveWeight_sum_telescope] at hu
  dsimp [x] at hu
  unfold qComparatorPathFluctuation
  nlinarith [hu]

/-- Actual lower decomposition: its fluctuation is the negative of the
centered-comparator sum; no sign-symmetry assumption is used. -/
theorem qComparator_minus_unroll (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ Q : State → Action → ℝ)
    (L t : ℕ) (hLt : L ≤ t) (s : State) (a : Action) :
    Q s a - qLearningIterate M η samples Q₀ t s a =
      (∏ j ∈ Finset.Icc (L+1) t, (1 - η j)) * (Q s a - qLearningIterate M η samples Q₀ L s a) +
      M.discount * (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (qLearningValue M Q (samples i s a) -
          qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a))) -
      qComparatorPathFluctuation M η samples Q L t s a -
      (1 - ∏ j ∈ Finset.Icc (L+1) t, (1 - η j)) * qComparatorResidualMinus M Q s a := by
  let x := fun i ↦ Q s a - qLearningIterate M η samples Q₀ i s a
  let f := fun i ↦ M.discount *
      (qLearningValue M Q (samples i s a) -
        qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a)) +
    M.discount * (-(qLearningValue M Q (samples i s a) -
      (M.transition s a).expectation (qLearningValue M Q))) - qComparatorResidualMinus M Q s a
  have hx : ∀ i, L < i → i ≤ t → x i = (1 - η i) * x (i-1) + η i * f i := by
    intro i hi hit
    have h := qComparator_minus_oneStep M η samples Q₀ Q (i-1) s a
    have he : i-1+1 = i := by omega
    rw [he] at h
    dsimp [x, f]
    nlinarith [h]
  have hu := qScalarRecurrence_unroll η x f L t hLt hx
  have hs := qComparator_weighted_affine_sum (Finset.Icc (L+1) t) (qPositiveWeight η t)
    (fun i ↦ qLearningValue M Q (samples i s a) -
      qLearningValue M (qLearningIterate M η samples Q₀ (i-1)) (samples i s a))
    (fun i ↦ -(qLearningValue M Q (samples i s a) - (M.transition s a).expectation (qLearningValue M Q)))
    M.discount (qComparatorResidualMinus M Q s a)
  change (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i * f i) = _ at hs
  rw [hs, qPositiveWeight_sum_telescope] at hu
  have hn : (∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
      -(qLearningValue M Q (samples i s a) - (M.transition s a).expectation (qLearningValue M Q))) =
      -(∑ i ∈ Finset.Icc (L+1) t, qPositiveWeight η t i *
        (qLearningValue M Q (samples i s a) - (M.transition s a).expectation (qLearningValue M Q))) := by
    simp only [mul_neg, Finset.sum_neg_distrib]
  rw [hn] at hu
  dsimp [x] at hu
  unfold qComparatorPathFluctuation
  nlinarith [hu]

end StatisticalRL.QLearning
