import Formalization.MDP.Basic
import Formalization.Analysis.Contraction

open Filter
open scoped Topology NNReal
namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The discount factor viewed as a nonnegative contraction constant. -/
def discountConstant (M : DiscountedMDP State Action) : ℝ≥0 :=
  ⟨M.discount, M.discount_nonneg⟩

@[simp]
theorem coe_discountConstant (M : DiscountedMDP State Action) :
    (M.discountConstant : ℝ) = M.discount := rfl

theorem qBellman_lipschitz (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    LipschitzWith M.discountConstant (M.qBellman π) := by
  apply LipschitzWith.of_dist_le_mul
  intro Q₁ Q₂
  simpa only [dist_eq_norm, coe_discountConstant] using M.norm_qBellman_sub_le π Q₁ Q₂

theorem qOptimality_lipschitz (M : DiscountedMDP State Action) :
    LipschitzWith M.discountConstant M.qOptimality := by
  apply LipschitzWith.of_dist_le_mul
  intro Q₁ Q₂
  simpa only [dist_eq_norm, coe_discountConstant] using M.norm_qOptimality_sub_le Q₁ Q₂

theorem qBellman_contracting (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ContractingWith M.discountConstant (M.qBellman π) :=
  ⟨M.discount_lt_one, M.qBellman_lipschitz π⟩

theorem qOptimality_contracting (M : DiscountedMDP State Action) :
    ContractingWith M.discountConstant M.qOptimality :=
  ⟨M.discount_lt_one, M.qOptimality_lipschitz⟩

/-- The actual policy Bellman equation has exactly one solution. -/
theorem policy_fixedPoint_exists_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ∃! Q : State → Action → ℝ, M.qBellman π Q = Q :=
  StatisticalRL.Analysis.contraction_exists_unique (M.qBellman_contracting π)

/-- The actual Bellman optimality equation has exactly one solution. -/
theorem optimality_fixedPoint_exists_unique (M : DiscountedMDP State Action) :
    ∃! Q : State → Action → ℝ, M.qOptimality Q = Q :=
  StatisticalRL.Analysis.contraction_exists_unique M.qOptimality_contracting


end StatisticalRL.DiscountedMDP
