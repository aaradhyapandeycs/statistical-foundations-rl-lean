import Formalization.Probability.EmpiricalBernsteinSharp.FiniteBinaryTensorization
import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductCoordinateSplit
import Formalization.Probability.EmpiricalBernsteinSharp.FiniteEntropyLogRatio

/-! Private uncompiled finite iid product entropy tensorization. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

noncomputable def finiteSampleEntropy {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (F : (Fin n → State) → ℝ) : ℝ :=
  (∑ ω, (∏ i, p (ω i)) * (F ω * Real.log (F ω))) -
    (∑ ω, (∏ i, p (ω i)) * F ω) * Real.log (∑ ω, (∏ i, p (ω i)) * F ω)

noncomputable def finiteSampleCoordinateEntropy {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (F : (Fin n → State) → ℝ) (j : Fin n) : ℝ :=
  ∑ ω, (∏ i, p (ω i)) *
    (F ω * Real.log (F ω / ∑ s, p s * F (Function.update ω j s)))

/-- One induction step: split off the first iid coordinate. -/
theorem finite_sample_entropy_succ_le {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (F : (Fin (n+1) → State) → ℝ) (hF : ∀ ω, 0 < F ω) :
    finiteSampleEntropy p (n+1) F ≤ finiteSampleCoordinateEntropy p (n+1) F 0 +
      ∑ head : State, p head * finiteSampleEntropy p n (fun tail ↦ F (Fin.cons head tail)) := by
  classical
  let q : (Fin n → State) → ℝ := fun tail ↦ ∏ i, p (tail i)
  let G : State → (Fin n → State) → ℝ := fun head tail ↦ F (Fin.cons head tail)
  have hq (tail : Fin n → State) : 0 ≤ q tail := Finset.prod_nonneg (fun i hi ↦ hp _)
  have hq1 : ∑ tail, q tail = 1 := finite_sample_product_mass_sum p hp1 n
  have hG (head : State) (tail : Fin n → State) : 0 < G head tail := hF _
  have hb := finite_binary_entropy_tensorization p q G hp hq hp1 hq1 hG
  have hleft : finiteSampleEntropy p (n+1) F =
      (∑ head, p head * ∑ tail, q tail * (G head tail * Real.log (G head tail))) -
      (∑ head, p head * ∑ tail, q tail * G head tail) *
        Real.log (∑ head, p head * ∑ tail, q tail * G head tail) := by
    dsimp [finiteSampleEntropy, q, G]
    rw [finite_sample_product_expectation_head_tail,
      finite_sample_product_expectation_head_tail]
  have hfirst :
      (∑ tail, q tail * ((∑ head, p head * (G head tail * Real.log (G head tail))) -
        (∑ head, p head * G head tail)*Real.log (∑ head, p head * G head tail))) =
      finiteSampleCoordinateEntropy p (n+1) F 0 := by
    dsimp [finiteSampleCoordinateEntropy, q, G]
    rw [finite_sample_head_coordinate_entropy]
    apply Finset.sum_congr rfl
    intro tail htail
    congr 1
    exact finite_entropy_eq_log_ratio p (fun head ↦ F (Fin.cons head tail)) hp hp1
      (fun head ↦ hF _)
  rw [← hleft, hfirst] at hb
  exact hb

/-- Finite iid entropy is bounded by the sum of its coordinate entropies. -/
theorem finite_sample_entropy_tensorization {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (F : (Fin n → State) → ℝ) (hF : ∀ ω, 0 < F ω) :
    finiteSampleEntropy p n F ≤ ∑ j : Fin n, finiteSampleCoordinateEntropy p n F j := by
  classical
  induction n with
  | zero => simp [finiteSampleEntropy, finiteSampleCoordinateEntropy]
  | succ n ih =>
      have hstep := finite_sample_entropy_succ_le p hp hp1 n F hF
      have htail : (∑ head : State, p head *
          finiteSampleEntropy p n (fun tail ↦ F (Fin.cons head tail))) ≤
          ∑ head : State, p head * ∑ j : Fin n,
            finiteSampleCoordinateEntropy p n (fun tail ↦ F (Fin.cons head tail)) j := by
        apply Finset.sum_le_sum
        intro head hhead
        exact mul_le_mul_of_nonneg_left (ih (fun tail ↦ F (Fin.cons head tail))
          (fun tail ↦ hF _)) (hp head)
      have htailEq : (∑ head : State, p head * ∑ j : Fin n,
          finiteSampleCoordinateEntropy p n (fun tail ↦ F (Fin.cons head tail)) j) =
          ∑ j : Fin n, finiteSampleCoordinateEntropy p (n+1) F j.succ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [finiteSampleCoordinateEntropy]
        exact (finite_sample_tail_coordinate_entropy p n F j).symm
      rw [Fin.sum_univ_succ, ← htailEq]
      exact hstep.trans (add_le_add le_rfl htail)

end StatisticalRL.EmpiricalBernsteinEntropy
