import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductTensorization
import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductResampling

/-! Private uncompiled identification of each coordinate entropy as an
average of finite conditional entropies. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_coordinate_entropy_as_conditional {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (G : (Fin n → State) → ℝ) (hG : ∀ ω, 0 < G ω) (j : Fin n) :
    finiteSampleCoordinateEntropy p n G j =
      ∑ ω : Fin n → State, (∏ i, p (ω i)) *
        ((∑ s, p s * (G (Function.update ω j s) * Real.log (G (Function.update ω j s)))) -
          (∑ s, p s * G (Function.update ω j s)) *
            Real.log (∑ s, p s * G (Function.update ω j s))) := by
  classical
  let L : (Fin n → State) → ℝ := fun ω ↦
    G ω * Real.log (G ω / ∑ s, p s * G (Function.update ω j s))
  have hres := finite_sample_resampling_invariant p hp1 n L j
  have hL (ω : Fin n → State) (s : State) :
      L (Function.update ω j s) = G (Function.update ω j s) *
        Real.log (G (Function.update ω j s) /
          ∑ z, p z * G (Function.update ω j z)) := by
    simp only [L, Function.update_idem]
  simp_rw [hL] at hres
  have hcond (ω : Fin n → State) :
      (∑ s, p s * (G (Function.update ω j s) *
        Real.log (G (Function.update ω j s) / ∑ z, p z * G (Function.update ω j z)))) =
      (∑ s, p s * (G (Function.update ω j s) * Real.log (G (Function.update ω j s)))) -
        (∑ s, p s * G (Function.update ω j s)) *
          Real.log (∑ s, p s * G (Function.update ω j s)) := by
    exact (finite_entropy_eq_log_ratio p (fun s ↦ G (Function.update ω j s)) hp hp1
      (fun s ↦ hG _)).symm
  simp_rw [hcond] at hres
  exact hres.symm

end StatisticalRL.EmpiricalBernsteinEntropy
