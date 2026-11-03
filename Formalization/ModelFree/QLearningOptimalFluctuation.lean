import Formalization.ModelFree.QLearningSynchronousSampling
import Formalization.MDP.OptimalTrajectoryValue

/-! Fixed-terminal optimal-value Q-learning fluctuation. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptFluctStateMeasurable : MeasurableSpace State := ⊤
local instance qOptFluctActionMeasurable : MeasurableSpace Action := ⊤

/-- Source η_i^(u), on the positive update indices used in ξ_u. The source's
separate i=0 weight is not used here. -/
noncomputable def qPositiveWeight (η : ℕ → ℝ) (u i : ℕ) : ℝ :=
  η i * ∏ j ∈ Finset.Icc (i+1) u, (1 - η j)

/-- The actual trajectory value of an optimal greedy policy, fixed before samples. -/
noncomputable def qTrueOptimalValue (M : DiscountedMDP State Action) : State → ℝ :=
  M.trajectoryExpectedValue M.optimalGreedyPolicy

/-- At fixed terminal u≤T, layer t represents source update i=t+1. Contributions
outside floor(T/2)<i≤u are zero, including all layers t≥T. -/
noncomputable def qOptimalFluctuationIncrement (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (T u : ℕ) (s : State) (a : Action) (t : ℕ)
    (data : QSamples State Action T) : ℝ :=
  if ht : t < T ∧ T / 2 < t+1 ∧ t+1 ≤ u then
    M.discount * qPositiveWeight η u (t+1) *
      (qTrueOptimalValue M (data ((s,a), ⟨t,ht.1⟩)) -
        (M.transition s a).expectation (qTrueOptimalValue M))
  else 0

/-- Fixed-terminal ξ_u(s,a) is the sum of its T actual sample layers. -/
noncomputable def qOptimalFluctuation (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T u : ℕ) (s : State) (a : Action) (data : QSamples State Action T) : ℝ :=
  ∑ t ∈ Finset.range T, qOptimalFluctuationIncrement M η T u s a t data

/- Moments, history, source indexing and the fixed-row Freedman bound are established in subsequent modules. -/
end StatisticalRL.QLearning
