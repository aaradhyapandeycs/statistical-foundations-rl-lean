import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductSelfBoundEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Private uncompiled differentiation of the finite iid self-bounding
Laplace transform. The differential inequality is not an MGF conclusion. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

noncomputable def finiteSampleLaplace {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (f : (Fin n → State) → ℝ) (theta : ℝ) : ℝ :=
  ∑ ω, (∏ i, p (ω i)) * Real.exp (-theta*f ω)

noncomputable def finiteSampleTiltedFirstMoment {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (f : (Fin n → State) → ℝ) (theta : ℝ) : ℝ :=
  ∑ ω, (∏ i, p (ω i)) * (Real.exp (-theta*f ω)*f ω)

theorem finite_sample_laplace_derivative {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (f : (Fin n → State) → ℝ) (theta : ℝ) :
    HasDerivAt (finiteSampleLaplace p n f)
      (-finiteSampleTiltedFirstMoment p n f theta) theta := by
  classical
  unfold finiteSampleLaplace finiteSampleTiltedFirstMoment
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun ω _ ↦
    (((hasDerivAt_id theta).neg.mul_const (f ω)).exp.const_mul (∏ i, p (ω i))))
  convert h using 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  simp only [Pi.neg_apply, id_eq]
  ring

theorem finite_sample_log_laplace_differential {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (f : (Fin n → State) → ℝ)
    (fi : Fin n → (Fin n → State) → ℝ) (a theta : ℝ)
    (ha : 0 < a) (htheta : 0 ≤ theta)
    (hind : ∀ j ω s, fi j (Function.update ω j s) = fi j ω)
    (hdec : ∀ j ω, 0 ≤ f ω-fi j ω ∧ f ω-fi j ω ≤ 1)
    (hsq : ∀ ω, (∑ j, (f ω-fi j ω)^2) ≤ a*f ω) :
    let M := finiteSampleLaplace p n f theta
    let A := finiteSampleTiltedFirstMoment p n f theta
    0 < M ∧ HasDerivAt (fun t ↦ Real.log (finiteSampleLaplace p n f t)) (-A/M) theta ∧
      (theta + a*(Real.exp theta-1-theta)) * (-A/M) ≤ Real.log M := by
  classical
  let M := finiteSampleLaplace p n f theta
  let A := finiteSampleTiltedFirstMoment p n f theta
  have hmass : (∑ ω : Fin n → State, ∏ i, p (ω i)) = 1 :=
    finite_sample_product_mass_sum p hp1 n
  have hw (ω : Fin n → State) : 0 ≤ ∏ i, p (ω i) := Finset.prod_nonneg (fun i hi ↦ hp _)
  have hwex : ∃ ω : Fin n → State, 0 < ∏ i, p (ω i) := by
    by_contra h
    push_neg at h
    have hs : (∑ ω : Fin n → State, ∏ i, p (ω i)) ≤ 0 :=
      Finset.sum_nonpos (fun ω _ ↦ h ω)
    linarith
  obtain ⟨ω₀, hω₀⟩ := hwex
  have hM : 0 < M := by
    dsimp [M, finiteSampleLaplace]
    apply Finset.sum_pos' (fun ω _ ↦ mul_nonneg (hw ω) (Real.exp_nonneg _))
    exact ⟨ω₀, Finset.mem_univ _, mul_pos hω₀ (Real.exp_pos _)⟩
  have hderiv := (finite_sample_laplace_derivative p n f theta).log (ne_of_gt hM)
  have hent := finite_sample_self_bound_entropy p hp hp1 n f fi a theta htheta hind hdec hsq
  have hsum : (∑ ω : Fin n → State, (∏ i, p (ω i)) *
      (Real.exp (-theta*f ω)*(-theta*f ω))) = -theta*A := by
    dsimp [A, finiteSampleTiltedFirstMoment]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  have hidentity : finiteSampleEntropy p n (fun ω ↦ Real.exp (-theta*f ω)) =
      -theta*A-M*Real.log M := by
    change (∑ ω : Fin n → State, (∏ i, p (ω i)) *
      (Real.exp (-theta*f ω)*Real.log (Real.exp (-theta*f ω)))) - M*Real.log M = _
    simp only [Real.log_exp]
    rw [hsum]
  rw [hidentity] at hent
  change -theta*A-M*Real.log M ≤ (Real.exp theta-1-theta)*a*A at hent
  have hineq : (theta+a*(Real.exp theta-1-theta))*(-A/M) ≤ Real.log M := by
    have hnum : (theta+a*(Real.exp theta-1-theta))*(-A) ≤ Real.log M*M := by
      nlinarith [hent]
    have hq : ((theta+a*(Real.exp theta-1-theta))*(-A))/M ≤ Real.log M :=
      (div_le_iff₀ hM).2 hnum
    simpa only [mul_div_assoc] using hq
  exact ⟨hM, by simpa [M, A] using hderiv, hineq⟩

/-- A nonnegative statistic has a Laplace transform at most one for a
nonnegative parameter. -/
theorem finite_sample_laplace_le_one {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (f : (Fin n → State) → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (theta : ℝ) (htheta : 0 ≤ theta) : finiteSampleLaplace p n f theta ≤ 1 := by
  classical
  unfold finiteSampleLaplace
  calc
    _ ≤ ∑ ω : Fin n → State, ∏ i, p (ω i) := by
      apply Finset.sum_le_sum
      intro ω hω
      have hw : 0 ≤ ∏ i, p (ω i) := Finset.prod_nonneg (fun i hi ↦ hp _)
      have he : Real.exp (-theta*f ω) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [mul_nonneg htheta (hf ω)]
      simpa using mul_le_mul_of_nonneg_left he hw
    _ = 1 := finite_sample_product_mass_sum p hp1 n

theorem finite_sample_laplace_zero {State : Type*} [Fintype State]
    (p : State → ℝ) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (f : (Fin n → State) → ℝ) : finiteSampleLaplace p n f 0 = 1 := by
  classical
  simp only [finiteSampleLaplace, zero_mul, neg_zero, Real.exp_zero, mul_one]
  exact finite_sample_product_mass_sum p hp1 n

end StatisticalRL.EmpiricalBernsteinEntropy
