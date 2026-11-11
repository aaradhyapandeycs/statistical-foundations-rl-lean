import Formalization.RobustRL.LowerBounds.LowerBound73Testing

/-!
# Corrected Theorem 7.3: the one-state case

With a single state every row is the point mass, so the TV ball is a singleton and the robust
value is the ordinary value. The two models share the (point-mass) kernel and differ only in
the reward `r_j(s,a) = 1[a = a_j]`; then `V_j^{π,σ}(s) = π(a_j|s)/(1-γ)` and
`V_j^{⋆,σ}(s) ≥ 1/(1-γ)`. This case uses that the estimator does not see the reward: under the
book's known-reward convention the one-state problem is degenerate (C38).
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound73

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

omit [DecidableEq State] in
theorem expectation_subsingleton [Subsingleton State] (d : FiniteDistribution State)
    (f : State → ℝ) (s : State) : d.expectation f = f s := by
  unfold FiniteDistribution.expectation
  rw [Fintype.sum_subsingleton _ s, d.prob_eq_one_of_subsingleton s, one_mul]

/-- One-state model: self-loop kernel, reward `1[a = g]`. -/
noncomputable def singleMDP [Nonempty State] (g : Action) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) : DiscountedMDP State Action where
  state_nonempty := inferInstance
  action_nonempty := ⟨g⟩
  transition s _ := pointMass s
  reward _ a := ell g 1 0 a
  reward_nonneg _ a := by unfold ell; split_ifs <;> norm_num
  reward_le_one _ a := by unfold ell; split_ifs <;> norm_num
  discount := γ
  discount_nonneg := hγ0
  discount_lt_one := hγ1

variable [Nonempty State] [Subsingleton State] (g : Action) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

omit [DecidableEq State] in
/-- Robust value in the one-state model: `π(g|s)/(1-γ)` for every radius `σ ≥ 0`. -/
theorem single_robustPolicyValue {σ : ℝ} (hσ0 : 0 ≤ σ) (π : StationaryPolicy State Action)
    (s : State) :
    robustPolicyValue tvBall (singleMDP g γ hγ0 hγ1) σ π s = (π s).prob g / (1 - γ) := by
  set M := singleMDP (State := State) g γ hγ0 hγ1
  have h1γ : (1 - γ) ≠ 0 := by linarith
  set W : State → ℝ := fun _ ↦ (π s).prob g / (1 - γ) with hW
  have hval : ∀ K : State → Action → FiniteDistribution State,
      (withKernel M K).trajectoryExpectedValue π s = (π s).prob g / (1 - γ) := by
    intro K
    have hfix : (withKernel M K).valueBellman π W = W := by
      funext t
      have ht : t = s := Subsingleton.elim t s
      subst ht
      rw [valueBellman_withKernel]
      have hfun : (fun a ↦ M.reward t a + M.discount * (K t a).expectation W) =
          fun a ↦ ell g 1 0 a + γ * ((π t).prob g / (1 - γ)) := by
        funext a
        rw [expectation_subsingleton _ _ t]
        rfl
      rw [hfun, FiniteDistribution.expectation_add, FiniteDistribution.expectation_const,
        expectation_ell]
      simp only [hW]
      field_simp
      ring
    rw [(withKernel M K).trajectoryExpectedValue_eq_valueFixedPoint,
      ← ((withKernel M K).valueFixedPoint_characterization π W).mp hfix]
  have hb : ∀ p : FiniteDistribution State, p ∈ (tvBall p σ : Set (FiniteDistribution State)) :=
    (HorizonTrap.tvBall_trapBall hσ0).self_mem
  have hset : {v | ∃ K, RobustAdmissible tvBall M σ K ∧
      v = (withKernel M K).trajectoryExpectedValue π s} = {(π s).prob g / (1 - γ)} := by
    ext v
    constructor
    · rintro ⟨K, -, rfl⟩
      exact hval K
    · intro hv
      rw [Set.mem_singleton_iff.mp hv]
      exact ⟨M.transition, fun _ _ ↦ hb _, (hval _).symm⟩
  unfold robustPolicyValue
  rw [hset, csInf_singleton]

omit [DecidableEq State] in
/-- One-state gap event: a policy with `π(g|s) ≤ 1/2` has robust gap `≥ 1/(2(1-γ))`. -/
theorem single_gap {σ : ℝ} (hσ0 : 0 ≤ σ) (π : StationaryPolicy State Action) (s : State)
    (hπ : (π s).prob g ≤ 1 / 2) :
    1 / (2 * (1 - γ)) ≤ robustOptimalValueAt tvBall (singleMDP g γ hγ0 hγ1) σ (pointMass s) -
      robustPolicyValueAt tvBall (singleMDP g γ hγ0 hγ1) σ π (pointMass s) := by
  have hb : ∀ p : FiniteDistribution State, p ∈ (tvBall p σ : Set (FiniteDistribution State)) :=
    (HorizonTrap.tvBall_trapBall hσ0).self_mem
  unfold robustOptimalValueAt robustPolicyValueAt
  rw [expectation_pointMass, expectation_pointMass]
  have hopt := HorizonTrap.robustPolicyValue_le_optimal tvBall (singleMDP g γ hγ0 hγ1) σ hb
    (detPolicy fun _ ↦ g) s
  rw [single_robustPolicyValue g hγ0 hγ1 hσ0] at hopt
  rw [single_robustPolicyValue g hγ0 hγ1 hσ0]
  have hdet : (detPolicy (fun _ : State ↦ g) s).prob g = 1 := by simp [detPolicy, pointMass]
  rw [hdet] at hopt
  have h1γ : 0 < 1 - γ := by linarith
  have : 1 / (2 * (1 - γ)) = 1 / (1 - γ) - (1 / 2) / (1 - γ) := by field_simp; ring
  have hle : (π s).prob g / (1 - γ) ≤ (1 / 2) / (1 - γ) :=
    div_le_div_of_nonneg_right hπ h1γ.le
  linarith

omit [Subsingleton State] in
/-- One-state testing bound: the two sampling laws coincide, so the error events of any
binary test have total probability at least `1/2`. -/
theorem single_test_sum (g₀ g₁ : Action) (N : ℕ)
    (E₀ E₁ : Set (ModelBasedPolicyLearning.Samples State Action N))
    (test : ModelBasedPolicyLearning.Samples State Action N → Bool)
    (h₀ : {x | test x = false} ⊆ E₀) (h₁ : {x | test x = true} ⊆ E₁) :
    1 / 2 ≤ (ModelBasedPolicyLearning.samplingLaw (singleMDP g₀ γ hγ0 hγ1) N).real E₀ +
      (ModelBasedPolicyLearning.samplingLaw (singleMDP g₁ γ hγ0 hγ1) N).real E₁ := by
  have hT := samplingLaw_test_sum (singleMDP g₀ γ hγ0 hγ1) (singleMDP g₁ γ hγ0 hγ1) N E₀ E₁
    test h₀ h₁
  have hrow : ∀ sa : State × Action,
      rowAff ((singleMDP (State := State) g₀ γ hγ0 hγ1).transition sa.1 sa.2)
        ((singleMDP (State := State) g₁ γ hγ0 hγ1).transition sa.1 sa.2) = 1 :=
    fun sa ↦ rowAff_self _
  simp only [hrow, one_pow, Finset.prod_const_one] at hT
  linarith

end StatisticalRL.RobustRL.Ch7.LowerBound73
