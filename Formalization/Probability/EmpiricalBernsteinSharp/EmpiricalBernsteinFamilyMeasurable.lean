import Formalization.Probability.EmpiricalBernsteinSharp.FiniteFamilyMeasurableExists
import Formalization.Probability.Variance

/-! Private uncompiled measurability of empirical-variance family violations.
No concentration or independence assumption is made here. -/
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]

noncomputable def empiricalBernsteinFamilyRadius (row : FiniteDistribution State)
    (N k : ℕ) (δ : ℝ) (V : State → ℝ) : ℝ :=
  Real.sqrt (2*row.variance V*Real.log (4*(k : ℝ)/δ)/((N : ℝ)-1)) +
    7*‖V‖*Real.log (4*(k : ℝ)/δ)/(3*((N : ℝ)-1))

theorem empiricalBernsteinFamily_vector_violation_measurable
    (d row : FiniteDistribution State) (N k : ℕ) (δ : ℝ) :
    MeasurableSet {V : State → ℝ | empiricalBernsteinFamilyRadius row N k δ V <
      |row.expectation V-d.expectation V|} := by
  have heval (q : FiniteDistribution State) : Measurable (fun V : State → ℝ ↦ q.expectation V) := by
    unfold FiniteDistribution.expectation
    exact Finset.measurable_sum _ (fun s _ ↦ measurable_const.mul (measurable_pi_apply s))
  have hsq : Measurable (fun V : State → ℝ ↦ row.expectation (fun s ↦ (V s)^2)) := by
    unfold FiniteDistribution.expectation
    exact Finset.measurable_sum _ (fun s _ ↦ measurable_const.mul ((measurable_pi_apply s).pow_const 2))
  have hvar : Measurable (fun V : State → ℝ ↦ row.variance V) := by
    simpa only [FiniteDistribution.variance] using hsq.sub ((heval row).pow_const 2)
  unfold empiricalBernsteinFamilyRadius
  have hr : Measurable (fun V : State → ℝ ↦
      Real.sqrt (2*row.variance V*Real.log (4*(k : ℝ)/δ)/((N : ℝ)-1))) :=
    (((measurable_const.mul hvar).mul_const _).div_const _).sqrt
  have hl : Measurable (fun V : State → ℝ ↦
      7*‖V‖*Real.log (4*(k : ℝ)/δ)/(3*((N : ℝ)-1))) :=
    (((measurable_const.mul measurable_id.norm).mul_const _).div_const _)
  exact measurableSet_lt (hr.add hl) ((heval row).sub (heval d)).abs

theorem empiricalBernsteinFamily_violation_measurable
    (d row : FiniteDistribution State) (N : ℕ) (δ : ℝ) :
    letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
    MeasurableSet {family : Finset (State → ℝ) | ∃ V ∈ family,
      empiricalBernsteinFamilyRadius row N family.card δ V <
        |row.expectation V-d.expectation V|} := by
  exact finiteFamilyBorel_exists_card_measurable
    (fun k V ↦ empiricalBernsteinFamilyRadius row N k δ V <
      |row.expectation V-d.expectation V|)
    (fun k ↦ empiricalBernsteinFamily_vector_violation_measurable d row N k δ)

end StatisticalRL.FiniteDistribution
