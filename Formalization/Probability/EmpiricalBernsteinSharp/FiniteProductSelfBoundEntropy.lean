import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductConditionalEntropy
import Formalization.Probability.EmpiricalBernsteinSharp.FiniteEntropySelfBoundCoordinate

/-! Private uncompiled finite-product self-bounding entropy estimate. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_self_bound_entropy {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (f : (Fin n → State) → ℝ)
    (fi : Fin n → (Fin n → State) → ℝ) (a theta : ℝ)
    (htheta : 0 ≤ theta)
    (hind : ∀ j ω s, fi j (Function.update ω j s) = fi j ω)
    (hdec : ∀ j ω, 0 ≤ f ω-fi j ω ∧ f ω-fi j ω ≤ 1)
    (hsq : ∀ ω, (∑ j, (f ω-fi j ω)^2) ≤ a*f ω) :
    finiteSampleEntropy p n (fun ω ↦ Real.exp (-theta*f ω)) ≤
      (Real.exp theta-1-theta)*a *
        ∑ ω : Fin n → State, (∏ i, p (ω i)) * (Real.exp (-theta*f ω)*f ω) := by
  classical
  let G : (Fin n → State) → ℝ := fun ω ↦ Real.exp (-theta*f ω)
  let ψ : ℝ := Real.exp theta-1-theta
  have hψ : 0 ≤ ψ := by dsimp [ψ]; linarith [Real.add_one_le_exp theta]
  have hweight (ω : Fin n → State) : 0 ≤ ∏ i, p (ω i) :=
    Finset.prod_nonneg (fun i hi ↦ hp _)
  have hcoord (j : Fin n) : finiteSampleCoordinateEntropy p n G j ≤
      ψ * ∑ ω : Fin n → State, (∏ i, p (ω i)) * (G ω*(f ω-fi j ω)^2) := by
    rw [finite_sample_coordinate_entropy_as_conditional p hp hp1 n G
      (fun ω ↦ Real.exp_pos _) j]
    have hlocal (ω : Fin n → State) :
        ((∑ s, p s * (G (Function.update ω j s) * Real.log (G (Function.update ω j s)))) -
          (∑ s, p s * G (Function.update ω j s)) *
            Real.log (∑ s, p s * G (Function.update ω j s))) ≤
        ψ * ∑ s, p s * (G (Function.update ω j s) *
          (f (Function.update ω j s)-fi j ω)^2) := by
      have h := finite_entropy_exp_decrement_le p (fun s ↦ f (Function.update ω j s))
        (fi j ω) theta hp hp1 htheta
        (fun s ↦ by simpa [hind] using (hdec j (Function.update ω j s)).1)
        (fun s ↦ by simpa [hind] using (hdec j (Function.update ω j s)).2)
      exact h
    have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) ↦
      mul_le_mul_of_nonneg_left (hlocal ω) (hweight ω))
    let R : (Fin n → State) → ℝ := fun ω ↦ G ω*(f ω-fi j ω)^2
    have hr := finite_sample_resampling_invariant p hp1 n R j
    have heq (ω : Fin n → State) (s : State) :
        R (Function.update ω j s) = G (Function.update ω j s) *
          (f (Function.update ω j s)-fi j ω)^2 := by simp only [R, hind]
    simp_rw [heq] at hr
    have hfactor : (∑ ω : Fin n → State, (∏ i, p (ω i)) *
        (ψ * ∑ s, p s * (G (Function.update ω j s) *
          (f (Function.update ω j s)-fi j ω)^2))) =
        ψ * ∑ ω : Fin n → State, (∏ i, p (ω i)) * (G ω*(f ω-fi j ω)^2) := by
      change (∑ ω : Fin n → State, (∏ i, p (ω i)) *
        (ψ * ∑ s, p s * (G (Function.update ω j s) *
          (f (Function.update ω j s)-fi j ω)^2))) =
        ψ * ∑ ω : Fin n → State, (∏ i, p (ω i)) * R ω
      rw [← hr, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    rw [hfactor] at hsum
    exact hsum
  have htens := finite_sample_entropy_tensorization p hp hp1 n G (fun ω ↦ Real.exp_pos _)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hcoord j)
  have hpoint (ω : Fin n → State) :
      (∑ j, (∏ i, p (ω i)) * (G ω*(f ω-fi j ω)^2)) ≤
        (∏ i, p (ω i)) * (G ω*(a*f ω)) := by
    have hh := mul_le_mul_of_nonneg_left (hsq ω)
      (mul_nonneg (hweight ω) (Real.exp_nonneg (-theta*f ω)))
    simpa only [Finset.mul_sum, mul_assoc] using hh
  have htotal := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) ↦ hpoint ω)
  calc
    _ ≤ ∑ j, finiteSampleCoordinateEntropy p n G j := htens
    _ ≤ ∑ j, ψ * ∑ ω : Fin n → State, (∏ i, p (ω i)) * (G ω*(f ω-fi j ω)^2) := hsum
    _ = ψ * ∑ ω : Fin n → State, ∑ j,
        (∏ i, p (ω i)) * (G ω*(f ω-fi j ω)^2) := by
      calc
        _ = ψ * ∑ j, ∑ ω : Fin n → State,
            (∏ i, p (ω i)) * (G ω*(f ω-fi j ω)^2) := (Finset.mul_sum _ _ _).symm
        _ = _ := by rw [Finset.sum_comm]
    _ ≤ ψ * ∑ ω : Fin n → State, (∏ i, p (ω i)) * (G ω*(a*f ω)) :=
      mul_le_mul_of_nonneg_left htotal hψ
    _ = _ := by
      dsimp [ψ, G]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring

end StatisticalRL.EmpiricalBernsteinEntropy
