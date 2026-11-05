import Formalization.MDP.CoreDefinitions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Instances.Matrix

/-! Policy transition matrices for arbitrary stationary randomized policies. -/
open scoped BigOperators Matrix
namespace StatisticalRL
namespace DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

def policyStateTransitionMatrix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : Matrix State State ℝ :=
  fun s t => ∑ a, (π s).prob a * (M.transition s a).prob t

def policyStateActionTransitionMatrix (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : Matrix (State × Action) (State × Action) ℝ :=
  fun sa tb => (M.transition sa.1 sa.2).prob tb.1 * (π tb.1).prob tb.2

end DiscountedMDP

def stochasticResolventProperties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (γ : ℝ) : Prop :=
  IsUnit (1 - γ • P) ∧
  (1 - γ • P)⁻¹ = 1 + ∑' n : ℕ, (γ • P)^(n + 1) ∧
  (1 - γ • P)⁻¹ *ᵥ (fun _ => 1) = (fun _ => 1 / (1 - γ)) ∧
  ‖fun i => ∑ j, |((1 - γ • P)⁻¹) i j|‖ = 1 / (1 - γ) ∧
  ∀ i j, 0 ≤ ((1 - γ • P)⁻¹) i j

end StatisticalRL
