import Formalization.Probability.EmpiricalHoeffding

/-! Private fixed-row deterministic-weight MGF prerequisite. It does not claim
concentration for random visit counts or the adaptive trajectory. -/
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance qLearningWeightedRowStateMeasurable : MeasurableSpace State := ⊤

/-- Any deterministic real weights preserve row-coordinate independence, and
have the sum of the individually scaled Hoeffding proxies. -/
theorem qLearning_weightedRow_subgaussian (d : FiniteDistribution State)
    (V : State → ℝ) (N : ℕ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (w : Fin N → ℝ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i : Fin N, w i * d.centeredSample V N i ω)
      (∑ i : Fin N, ‖w i‖₊ ^ 2 * (‖B‖₊ / 2)^2)
      (d.sampleMeasure N) := by
  have hi := (d.centeredSample_independent V N).comp
    (fun i x ↦ w i * x) (fun _ ↦ measurable_const.mul measurable_id)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ)
    (c := fun i ↦ ‖w i‖₊ ^ 2 * (‖B‖₊ / 2)^2)
    (fun i _ ↦ by
      have heq : (⟨(w i)^2, sq_nonneg (w i)⟩ : ℝ≥0) = ‖w i‖₊ ^ 2 := by
        ext
        change (w i)^2 = ((‖w i‖₊ : ℝ≥0) : ℝ)^2
        rw [coe_nnnorm, Real.norm_eq_abs, sq_abs]
      dsimp only
      rw [← heq]
      exact (d.centeredSample_subgaussian V N i B hV).const_mul (w i))
  simpa using h
end StatisticalRL.FiniteDistribution
