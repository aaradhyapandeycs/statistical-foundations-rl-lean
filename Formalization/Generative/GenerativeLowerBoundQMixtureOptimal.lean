import Formalization.Generative.GenerativeLowerBoundQMixtureFamily
import Formalization.Generative.GenerativeLowerBoundParameters

/-! Actual optimal trajectory Q for the one-row-change mixture family. -/
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.DiscountedMDP

/-- In each active state, some action attains the best stay probability. -/
theorem qMixtureStay_best_attained {m A : ℕ} [NeZero A] (i : QMixtureIndex m A)
    (p q : ℝ) (j : Fin m) :
    ∃ a : Fin A, qMixtureStay i p q j a = qMixtureBestStay i p q j := by
  classical
  by_cases h : ∃ a : Fin A, i = some (j,a)
  · obtain ⟨a, ha⟩ := h
    exact ⟨a, by simp [qMixtureStay, qMixtureBestStay, ha, show ∃ b, i = some (j,b) from ⟨a, ha⟩]⟩
  · refine ⟨0, ?_⟩
    simp [qMixtureStay, qMixtureBestStay, h, fun a ↦ not_exists.mp h a]

/-- The actual best row lies between p and q. -/
theorem qMixtureStay_le_best {m A : ℕ} (i : QMixtureIndex m A)
    (p q : ℝ) (hpq : p ≤ q) (j : Fin m) (a : Fin A) :
    qMixtureStay i p q j a ≤ qMixtureBestStay i p q j := by
  classical
  unfold qMixtureStay qMixtureBestStay
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact False.elim (h₂ ⟨a, h₁⟩)
  · exact hpq
  · exact le_rfl

/-- Action maximization of the proposed Q expression uses the best row. -/
theorem qMixtureOptimalQ_actionMaximum {m A : ℕ} [NeZero A] (i : QMixtureIndex m A)
    (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) (j : Fin m) :
    actionMaximum (qMixtureOptimalQCandidate i γ p q (some j)) =
      1 / (1 - γ * qMixtureBestStay i p q j) := by
  classical
  have hbest : qMixtureBestStay i p q j ≤ q := by
    unfold qMixtureBestStay
    split <;> linarith
  have hden : 0 < 1 - γ * qMixtureBestStay i p q j := by
    have h := mul_le_mul_of_nonneg_left hbest hγ
    have h' := mul_le_mul_of_nonneg_left hq.le hγ
    nlinarith
  obtain ⟨a₀, ha₀⟩ := qMixtureStay_best_attained i p q j
  have hgood : qMixtureOptimalQCandidate i γ p q (some j) a₀ =
      1 / (1 - γ * qMixtureBestStay i p q j) := by
    simp only [qMixtureOptimalQCandidate, ha₀]
    field_simp
    ring
  have hmax (a : Fin A) : qMixtureOptimalQCandidate i γ p q (some j) a ≤
      qMixtureOptimalQCandidate i γ p q (some j) a₀ := by
    simp only [qMixtureOptimalQCandidate, ha₀]
    apply add_le_add_right _ 1
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_left (qMixtureStay_le_best i p q hpq j a) hγ
  apply le_antisymm
  · rw [← hgood]
    exact (Finset.sup'_le_iff Finset.univ_nonempty _).2 (fun a _ ↦ hmax a)
  · rw [← hgood]
    exact le_actionMaximum _ _

/-- The candidate is the optimal Bellman fixed point of the actual MDP. -/
theorem qMixtureOptimalQ_eq_fixedPoint {m A : ℕ} [NeZero A] (i : QMixtureIndex m A)
    (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1) :
    qMixtureOptimalQCandidate i γ p q =
      (qMixtureMDP i γ p q hγ hγ1 hp hpq hq).optimalityFixedPoint := by
  let M := qMixtureMDP i γ p q hγ hγ1 hp hpq hq
  let Q := qMixtureOptimalQCandidate i γ p q
  have hnone : actionMaximum (Q none) = 0 := by
    unfold Q qMixtureOptimalQCandidate actionMaximum
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
    change 1 + γ * (familyActiveRow j (qMixtureStay i p q j a) _ _).expectation
      (fun t ↦ actionMaximum (Q t)) =
        1 + γ * qMixtureStay i p q j a / (1 - γ * qMixtureBestStay i p q j)
    rw [familyActiveRow_expectation, hnone,
      qMixtureOptimalQ_actionMaximum i γ p q hγ hγ1 hp hpq hq]
    ring

/-- The fixed point formula is the actual optimal forced-action trajectory Q. -/
theorem qMixtureMDP_optimal_trajectoryQ {m A : ℕ} [NeZero A]
    (i : QMixtureIndex m A) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1)
    (s : Option (Fin m)) (a : Fin A) :
    let M := qMixtureMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a = qMixtureOptimalQCandidate i γ p q s a := by
  dsimp only
  rw [DiscountedMDP.optimalGreedy_trajectoryQ]
  exact congrFun (congrFun (qMixtureOptimalQ_eq_fixedPoint i γ p q hγ hγ1 hp hpq hq).symm s) a

/-- The actual baseline/alternative Q values differ by more than 2ε at the
same changed forced-action coordinate under the source parameter choices. -/
theorem qMixtureMDP_source_separation {m A : ℕ} [NeZero A] (j : Fin m) (a : Fin A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) :
    let p := baseProbability γ
    let q := p + probabilityIncrement γ ε
    let M₀ := qMixtureMDP (none : QMixtureIndex m A) γ p q (by linarith) hγ1
      (by linarith [source_parameters_admissible γ ε hγ hγ1 hε hεmax])
      (by linarith [source_parameters_admissible γ ε hγ hγ1 hε hεmax])
      (by linarith [source_parameters_admissible γ ε hγ hγ1 hε hεmax])
    let M₁ := qMixtureMDP (some (j,a)) γ p q (by linarith) hγ1
      (by linarith [source_parameters_admissible γ ε hγ hγ1 hε hεmax])
      (by linarith [source_parameters_admissible γ ε hγ hγ1 hε hεmax])
      (by linarith [source_parameters_admissible γ ε hγ hγ1 hε hεmax])
    2 * ε < M₁.trajectoryExpectedQ M₁.optimalGreedyPolicy (some j) a -
      M₀.trajectoryExpectedQ M₀.optimalGreedyPolicy (some j) a := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  have hgap := source_parameters_scalar_separation γ ε hγ hγ1 hε hεmax
  dsimp only
  rw [qMixtureMDP_optimal_trajectoryQ, qMixtureMDP_optimal_trajectoryQ]
  simp [qMixtureOptimalQCandidate, qMixtureStay, qMixtureBestStay]
  have hpden : 1 - γ * baseProbability γ ≠ 0 := by
    have hp1 : baseProbability γ < 1 := by linarith [ha.2.1, ha.2.2.1]
    have h := mul_le_mul_of_nonneg_left hp1.le (show 0 ≤ γ by linarith)
    nlinarith
  have hqden : 1 - γ * (baseProbability γ + probabilityIncrement γ ε) ≠ 0 := by
    have h := mul_le_mul_of_nonneg_left ha.2.2.1.le (show 0 ≤ γ by linarith)
    nlinarith
  have hpval : 1 + γ * baseProbability γ / (1 - γ * baseProbability γ) =
      1 / (1 - γ * baseProbability γ) := by field_simp; ring
  have hqval : 1 + γ * (baseProbability γ + probabilityIncrement γ ε) /
      (1 - γ * (baseProbability γ + probabilityIncrement γ ε)) =
      1 / (1 - γ * (baseProbability γ + probabilityIncrement γ ε)) := by field_simp; ring
  linarith

end StatisticalRL.GenerativeLowerBound
