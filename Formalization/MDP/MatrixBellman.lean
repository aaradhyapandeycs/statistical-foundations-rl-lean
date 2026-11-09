import Formalization.MDP.FixedPoint
import Formalization.MDP.PolicyMatrixResolvent

/-! Matrix forms of the policy Bellman consistency equation
(`eq:Qpi-Vpi-matrix-notation-inf`, `chapters/prelim.tex:496–531`). -/

open scoped BigOperators Matrix
namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- (2.24a) pointwise: `Q^π(s,a) = r(s,a) + γ ∑_t P(t|s,a) V^π(t)` with
`V^π(t) = ∑_b π(b|t) Q^π(t,b)`. -/
theorem policyFixedPoint_eq_reward_add (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.policyFixedPoint π s a = M.reward s a + M.discount *
      ∑ t, (M.transition s a).prob t * ∑ b, (π t).prob b * M.policyFixedPoint π t b := by
  conv_lhs => rw [← M.policyFixedPoint_spec π]
  rfl

/-- The vector/matrix forms (2.24a–d) and the intermediate `Q^π = r + γP^πQ^π`. -/
theorem policyFixedPoint_matrix_forms (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    letI := Classical.decEq State
    letI := Classical.decEq Action
    let Q : State × Action → ℝ := fun sa ↦ M.policyFixedPoint π sa.1 sa.2
    let V : State → ℝ := fun s ↦ ∑ a, (π s).prob a * M.policyFixedPoint π s a
    let r : State × Action → ℝ := fun sa ↦ M.reward sa.1 sa.2
    let rπ : State → ℝ := fun s ↦ ∑ a, (π s).prob a * M.reward s a
    let P : Matrix (State × Action) State ℝ := fun sa t ↦ (M.transition sa.1 sa.2).prob t
    let γ := M.discount
    Q = r + γ • (P *ᵥ V) ∧
    V = rπ + γ • (M.policyStateTransitionMatrix π *ᵥ V) ∧
    V = (1 - γ • M.policyStateTransitionMatrix π)⁻¹ *ᵥ rπ ∧
    Q = r + γ • (M.policyStateActionTransitionMatrix π *ᵥ Q) ∧
    Q = (1 - γ • M.policyStateActionTransitionMatrix π)⁻¹ *ᵥ r := by
  letI := Classical.decEq State
  letI := Classical.decEq Action
  intro Q V r rπ P γ
  have hQ : ∀ s a, M.policyFixedPoint π s a =
      M.reward s a + γ * ∑ t, (M.transition s a).prob t * V t :=
    fun s a ↦ M.policyFixedPoint_eq_reward_add π s a
  have ha : Q = r + γ • (P *ᵥ V) := by
    funext sa
    simp only [Q, r, P, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact hQ sa.1 sa.2
  have hb : V = rπ + γ • (M.policyStateTransitionMatrix π *ᵥ V) := by
    funext s
    have hV : V s = ∑ a, (π s).prob a *
        (M.reward s a + γ * ∑ t, (M.transition s a).prob t * V t) :=
      Finset.sum_congr rfl fun a _ ↦ by rw [← hQ s a]
    rw [hV]
    simp only [rπ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      policyStateTransitionMatrix, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  have hPQ : M.policyStateActionTransitionMatrix π *ᵥ Q = P *ᵥ V := by
    funext sa
    simp only [Q, V, P, Matrix.mulVec, dotProduct, policyStateActionTransitionMatrix,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  have hd : Q = r + γ • (M.policyStateActionTransitionMatrix π *ᵥ Q) := by
    rw [hPQ]; exact ha
  rcases M.policyMatrices_resolvent_properties π with ⟨⟨hPu, -⟩, ⟨hQu, -⟩⟩
  refine ⟨ha, hb, ?_, hd, ?_⟩
  · letI : Invertible (1 - γ • M.policyStateTransitionMatrix π) := hPu.invertible
    refine (Matrix.inv_mulVec_eq_vec ?_).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, eq_sub_iff_add_eq]
    exact hb.symm
  · letI : Invertible (1 - γ • M.policyStateActionTransitionMatrix π) := hQu.invertible
    refine (Matrix.inv_mulVec_eq_vec ?_).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, eq_sub_iff_add_eq]
    exact hd.symm

end StatisticalRL.DiscountedMDP
