import Formalization.Generative.GenerativeLowerBoundIndexGeometry
import Formalization.Generative.GenerativeLowerBoundTwoStateMDP

/-! Corrected global-action multi-hypothesis actual MDP family. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.DiscountedMDP

/-- The self-loop probability of the chosen active state/action row. -/
def familyStay {m n : ℕ} (i : HardFamilyIndex m n) (p q : ℝ)
    (j : Fin m) (a : Fin (n + 1)) : ℝ :=
  if a = hardPolicySignature i j then q else p

/-- A two-point row on the active state and the common absorber. -/
noncomputable def familyActiveRow {m : ℕ} (j : Fin m) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) : FiniteDistribution (Option (Fin m)) :=
  (hardRow r hr hr1 true).bind (fun b ↦ EnvironmentStage.pointMass (if b then some j else none))

/-- Exact expectation of the source active row. -/
theorem familyActiveRow_expectation {m : ℕ} (j : Fin m) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (V : Option (Fin m) → ℝ) :
    (familyActiveRow j r hr hr1).expectation V = r * V (some j) + (1 - r) * V none := by
  rw [familyActiveRow, FiniteDistribution.expectation_bind]
  simp_rw [EnvironmentStage.expectation_pointMass]
  simp [FiniteDistribution.expectation, hardRow]

/-- A source-family MDP with all global actions padded at the absorber. -/
noncomputable def familyMDP {m n : ℕ} (i : HardFamilyIndex m n) (γ p q : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) :
    DiscountedMDP (Option (Fin m)) (Fin (n + 1)) where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition s a := match s with
    | none => EnvironmentStage.pointMass none
    | some j => familyActiveRow j (familyStay i p q j a)
        (by unfold familyStay; split <;> linarith)
        (by unfold familyStay; split <;> linarith)
  reward s _ := match s with | none => 0 | some _ => 1
  reward_nonneg := by intro s a; cases s <;> simp
  reward_le_one := by intro s a; cases s <;> simp
  discount := γ
  discount_nonneg := hγ
  discount_lt_one := hγ1

/-- Correct forced-first-action Q candidate, retaining optimal continuation. -/
noncomputable def familyOptimalQ {m n : ℕ} (i : HardFamilyIndex m n) (γ p q : ℝ) :
    Option (Fin m) → Fin (n + 1) → ℝ :=
  fun s a ↦ match s with
    | none => 0
    | some j => 1 + γ * familyStay i p q j a / (1 - γ * q)

/-- The candidate's maximum is attained by the designated action. -/
theorem familyOptimalQ_actionMaximum {m n : ℕ} (i : HardFamilyIndex m n)
    (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) (j : Fin m) :
    actionMaximum (familyOptimalQ i γ p q (some j)) = 1 / (1 - γ * q) := by
  have hq0 : 0 ≤ q := le_trans hp hpq
  have hden : 0 < 1 - γ * q := by
    have h := mul_le_mul_of_nonneg_left hq.le hγ
    nlinarith
  have hgood : familyOptimalQ i γ p q (some j) (hardPolicySignature i j) =
      1 / (1 - γ * q) := by
    simp [familyOptimalQ, familyStay]
    field_simp
    ring
  have hmax (a : Fin (n + 1)) : familyOptimalQ i γ p q (some j) a ≤
      familyOptimalQ i γ p q (some j) (hardPolicySignature i j) := by
    simp only [familyOptimalQ, familyStay, ↓reduceIte]
    apply add_le_add_right _ 1
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_left _ hγ
    split <;> linarith
  apply le_antisymm
  · rw [← hgood]
    exact (Finset.sup'_le_iff Finset.univ_nonempty _).2 (fun a _ ↦ hmax a)
  · rw [← hgood]
    exact le_actionMaximum _ _

/-- The corrected first-action formula is the unique optimality Bellman
fixed point of the actual indexed MDP. -/
theorem familyOptimalQ_eq_optimalityFixedPoint {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) :
    familyOptimalQ i γ p q = (familyMDP i γ p q hγ hγ1 hp hpq hq).optimalityFixedPoint := by
  let M := familyMDP i γ p q hγ hγ1 hp hpq hq
  let Q := familyOptimalQ i γ p q
  have hnone : actionMaximum (Q none) = 0 := by
    unfold Q familyOptimalQ actionMaximum
    simp
  apply (M.optimalityFixedPoint_characterization Q).mp
  funext s a
  cases s with
  | none =>
    change 0 + γ * (EnvironmentStage.pointMass none).expectation
      (fun t ↦ actionMaximum (Q t)) = 0
    rw [EnvironmentStage.expectation_pointMass, hnone]
    ring
  | some j =>
    change 1 + γ * (familyActiveRow j (familyStay i p q j a) _ _).expectation
      (fun t ↦ actionMaximum (Q t)) =
        1 + γ * familyStay i p q j a / (1 - γ * q)
    rw [familyActiveRow_expectation, hnone,
      familyOptimalQ_actionMaximum i γ p q hγ hγ1 hp hpq hq]
    ring

/-- Actual optimal forced-action trajectory Q has the corrected source-family
formula, including bad first actions and all actions at the absorber. -/
theorem familyMDP_optimal_trajectoryQ {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1)
    (s : Option (Fin m)) (a : Fin (n + 1)) :
    let M := familyMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a = familyOptimalQ i γ p q s a := by
  dsimp only
  rw [DiscountedMDP.optimalGreedy_trajectoryQ]
  exact congrFun (congrFun (familyOptimalQ_eq_optimalityFixedPoint i γ p q hγ hγ1 hp hpq hq).symm s) a

/-- Actual optimal trajectory value is V₁ at every active state and zero
at the absorbing state. -/
theorem familyMDP_optimal_trajectoryValue {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) (s : Option (Fin m)) :
    let M := familyMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedValue M.optimalGreedyPolicy s =
      match s with | none => 0 | some _ => 1 / (1 - γ * q) := by
  let M := familyMDP i γ p q hγ hγ1 hp hpq hq
  change M.trajectoryExpectedValue M.optimalGreedyPolicy s = _
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation
      (M.trajectoryExpectedQ M.optimalGreedyPolicy s) = _
  rw [EnvironmentStage.expectation_pointMass, M.optimalGreedy_trajectoryQ,
    M.optimalGreedyAction_max, ← familyOptimalQ_eq_optimalityFixedPoint i γ p q hγ hγ1 hp hpq hq]
  cases s with
  | none => simp [familyOptimalQ, actionMaximum]
  | some j => exact familyOptimalQ_actionMaximum i γ p q hγ hγ1 hp hpq hq j

/-- A designated first action has Q*=V₁; an undesignated first action has
Q*=1+γpV₁, reflecting optimal continuation after the forced first action. -/
theorem familyMDP_optimal_trajectoryQ_active {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) (j : Fin m) (a : Fin (n + 1)) :
    let M := familyMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedQ M.optimalGreedyPolicy (some j) a =
      if a = hardPolicySignature i j then 1 / (1 - γ * q)
      else 1 + γ * p / (1 - γ * q) := by
  have hden : 0 < 1 - γ * q := by
    have h := mul_le_mul_of_nonneg_left hq.le hγ
    nlinarith
  dsimp only
  rw [familyMDP_optimal_trajectoryQ]
  by_cases ha : a = hardPolicySignature i j
  · simp [familyOptimalQ, familyStay, ha]
    field_simp
    ring
  · simp [familyOptimalQ, familyStay, ha]

/-- The source parameter choices instantiate every corrected indexed MDP. -/
noncomputable def sourceFamilyMDP {m n : ℕ} (i : HardFamilyIndex m n) (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    DiscountedMDP (Option (Fin m)) (Fin (n + 1)) := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  exact familyMDP i γ (baseProbability γ) (baseProbability γ + probabilityIncrement γ ε)
    (by linarith) hγ1 (by linarith [ha.1]) ha.2.1.le ha.2.2.1

/-- Source-indexed actual optimal trajectory Q has the corrected
forced-first-action formula, not the erroneous bad-action V₀ formula. -/
theorem sourceFamilyMDP_optimal_trajectoryQ {m n : ℕ}
    (i : HardFamilyIndex m n) (γ ε : ℝ)
    (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (j : Fin m) (a : Fin (n + 1)) :
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    M.trajectoryExpectedQ M.optimalGreedyPolicy (some j) a =
      if a = hardPolicySignature i j then
        1 / (1 - γ * (baseProbability γ + probabilityIncrement γ ε))
      else 1 + γ * baseProbability γ /
        (1 - γ * (baseProbability γ + probabilityIncrement γ ε)) := by
  dsimp only [sourceFamilyMDP]
  exact familyMDP_optimal_trajectoryQ_active _ _ _ _ _ _ _ _ _ _ _

end StatisticalRL.GenerativeLowerBound
