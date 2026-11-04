import Formalization.ModelFree.QLearningIterateBounds
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.Probability.Variance

open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Source finite χ² divergence, summing only coordinates with positive
nominal mass. The accompanying support condition is imposed separately. -/
noncomputable def qChiSquared (p q : FiniteDistribution State) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x), (q.prob x - p.prob x)^2 / p.prob x

/-- Source uncertainty ball, explicitly forbidding mass outside p's support. -/
noncomputable def qChiBall (p : FiniteDistribution State) (ρ : ℝ) : Set (FiniteDistribution State) :=
  {q | (∀ x, p.prob x = 0 → q.prob x = 0) ∧ qChiSquared p q ≤ ρ}

/-- Actual robust upper and lower expected-value sets; no totalized division at
zero can silently admit mass on the nominal zero support. -/
noncomputable def qRobustExpectations (p : FiniteDistribution State) (ρ : ℝ)
    (v : State → ℝ) : Set ℝ :=
  {z | ∃ q ∈ qChiBall p ρ, z = q.expectation v}

/-- Source robust upper operator; reward shift b is an operator term and is
not forced into the bounded-reward MDP structure. -/
noncomputable def qRobustBellmanPlus (M : DiscountedMDP State Action) (ρ b : ℝ)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  M.reward s a + b + M.discount * sSup (qRobustExpectations (M.transition s a) ρ (qLearningValue M Q))

/-- Source robust lower operator, using infimum and negative reward shift. -/
noncomputable def qRobustBellmanMinus (M : DiscountedMDP State Action) (ρ b : ℝ)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  M.reward s a - b + M.discount * sInf (qRobustExpectations (M.transition s a) ρ (qLearningValue M Q))

/-- Source upper residual, defined directly from an arbitrary Q value. -/
noncomputable def qComparatorResidualPlus (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  Q s a - M.reward s a - M.discount * (M.transition s a).expectation (qLearningValue M Q)

/-- Source lower residual, oriented as nominal Bellman value minus Q, so its
sign is verified from the infimum equation rather than presumed by symmetry. -/
noncomputable def qComparatorResidualMinus (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  M.reward s a + M.discount * (M.transition s a).expectation (qLearningValue M Q) - Q s a

end StatisticalRL.QLearning
