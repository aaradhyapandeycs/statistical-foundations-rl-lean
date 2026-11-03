import Formalization.Generative.PolicyEvaluationAuxiliaryBernstein
import Formalization.Generative.PolicyEvaluationResidualRecursion

/-! Actual-law simultaneous auxiliary error recursion from the derived
Bernstein event. No sharp auxiliary growth estimate is assumed. -/

open scoped Matrix
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance bernsteinRecursionStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State

/-- The exact level/state union logarithm in the simultaneous Bernstein event. -/
noncomputable def auxiliaryRecursionLog (m : ℕ) (δ : ℝ) : ℝ :=
  Real.log (4 * Fintype.card State * (m + 1) / δ)

/-- Its logarithm is positive on the actual MDP/confidence domain. -/
theorem auxiliaryRecursionLog_pos (M : DiscountedMDP State Action)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < auxiliaryRecursionLog (State := State) m δ := by
  letI : Nonempty State := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card State := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hp : (1 : ℝ) ≤ (Fintype.card State : ℝ) * ((m : ℝ) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hm)]
  apply Real.log_pos
  apply (lt_div_iff₀ hδ).2
  nlinarith

/-- The real sample experiment yields the conditional recursion simultaneously
through level m. The linear coefficient retains the exact Bernstein factor 1/3. -/
theorem auxiliaryValues_bernstein_recursion (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data | ∀ l : Fin (m + 1),
      ‖empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l‖ ≤
        M.discount * Real.sqrt (2 * auxiliaryRecursionLog (State := State) m δ / N) *
          (‖empiricalAuxiliaryValue M π N hN data (l + 1) - auxiliaryValue M π (l + 1)‖ +
            ‖auxiliaryValue M π (l + 1)‖) +
        M.discount * (2 * auxiliaryRecursionLog (State := State) m δ / (3 * N)) *
          ‖auxiliaryValue M π l‖ / (1 - M.discount)} := by
  let μ := samplingLaw M π N
  let L := auxiliaryRecursionLog (State := State) m δ
  let a := Real.sqrt (2 * L / N)
  let c := 2 * L / (3 * N)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := div_nonneg
    (mul_nonneg (by norm_num) (auxiliaryRecursionLog_pos M m δ hδ hδ1).le) (by positivity)
  let good : Set (Samples State N) := {data | ∀ (s : State) (l : Fin (m + 1)),
    |(empiricalPolicyRow N hN data s).expectation (auxiliaryValue M π l) -
      (M.policyTransition π s).expectation (auxiliaryValue M π l)| ≤
    a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) +
      2 * ‖auxiliaryValue M π l‖ * L / (3 * N)}
  have hs : 1 - δ < μ.real good := auxiliaryValues_bernstein_explicit M π N hN m δ hδ hδ1
  let target : Set (Samples State N) := {data | ∀ l : Fin (m + 1),
    ‖empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l‖ ≤
      M.discount * a *
        (‖empiricalAuxiliaryValue M π N hN data (l + 1) - auxiliaryValue M π (l + 1)‖ +
          ‖auxiliaryValue M π (l + 1)‖) +
      M.discount * c * ‖auxiliaryValue M π l‖ / (1 - M.discount)}
  have hsub : good ⊆ target := by
    intro data hd l
    apply auxiliary_residual_recursion_conditional M π N hN data l a c ha hc
    intro s
    simp only [Matrix.sub_mulVec, Pi.sub_apply, empiricalMatrix_mulVec,
      evaluationPolicyMatrix_mulVec]
    have hh := hd s l
    convert hh using 1
    dsimp [c]
    ring
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  change 1 - δ < μ.real target
  exact hs.trans_le hmono

end StatisticalRL.ModelBasedPolicyEvaluation
