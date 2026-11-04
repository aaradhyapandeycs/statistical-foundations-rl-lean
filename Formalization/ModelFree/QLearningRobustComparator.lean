import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.ModelFree.QLearningIterateBounds
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.Probability.Variance

/-! support-aware χ² comparator definitions. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The nominal transition is feasible whenever ρ≥0, including zero atoms. -/
theorem qChiBall_self (p : FiniteDistribution State) (ρ : ℝ) (hρ : 0 ≤ ρ) : p ∈ qChiBall p ρ := by
  constructor
  · intro x hx
    exact hx
  · simpa [qChiSquared] using hρ

/-- The robust expectation set is nonempty, before any compactness claim. -/
theorem qRobustExpectations_nonempty (p : FiniteDistribution State) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : State → ℝ) : (qRobustExpectations p ρ v).Nonempty := by
  exact ⟨p.expectation v, p, qChiBall_self p ρ hρ, rfl⟩

/-- The two residual signs follow directly from their own fixed-point equations. -/
theorem qComparatorResidualPlus_eq (M : DiscountedMDP State Action) (ρ b : ℝ)
    (Q : State → Action → ℝ) (hQ : qRobustBellmanPlus M ρ b Q = Q) (s : State) (a : Action) :
    qComparatorResidualPlus M Q s a = b + M.discount *
      (sSup (qRobustExpectations (M.transition s a) ρ (qLearningValue M Q)) -
        (M.transition s a).expectation (qLearningValue M Q)) := by
  have h := congrFun (congrFun hQ s) a
  dsimp [qRobustBellmanPlus] at h
  unfold qComparatorResidualPlus
  linarith

theorem qComparatorResidualMinus_eq (M : DiscountedMDP State Action) (ρ b : ℝ)
    (Q : State → Action → ℝ) (hQ : qRobustBellmanMinus M ρ b Q = Q) (s : State) (a : Action) :
    qComparatorResidualMinus M Q s a = b + M.discount *
      ((M.transition s a).expectation (qLearningValue M Q) -
        sInf (qRobustExpectations (M.transition s a) ρ (qLearningValue M Q))) := by
  have h := congrFun (congrFun hQ s) a
  dsimp [qRobustBellmanMinus] at h
  unfold qComparatorResidualMinus
  linarith

/- Nonempty bounded balls, operator contraction and actual fixed points are proved in QLearningRobustContraction. Attainment and the source χ² comparison estimates are separate. -/
end StatisticalRL.QLearning
