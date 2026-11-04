import Formalization.Statements.Ch4
import Formalization.ModelFree.TDIterateBounds
import Formalization.ModelFree.TDSquareEnergy
import Formalization.ModelFree.TDSourceVarianceProxyUniversal
import Formalization.ModelFree.QLearningIterateBounds
import Formalization.ModelFree.QLearningStabilityInfinityNorm
import Formalization.ModelFree.QLearningRobustContraction
import Formalization.ModelFree.QLearningSourceTheoremClosure

/-! Proofs of the Chapter 4 statement index from the existing exports. -/
namespace StatisticalRL.Statements.Ch4
open StatisticalRL.TemporalDifference StatisticalRL.QLearning
universe u v

theorem Lemma4_2_holds : Lemma4_2 := by
  intro State Action instS instA M π η samples V₀ T h₀ hη t ht
  have hused : ∀ k, k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
    fun k hk ↦ hη k (hk.trans ht)
  exact ⟨fun s ↦ tdIterate_bounds M π η samples V₀ h₀ t hused s,
    tdIterate_error_norm_le M π η samples V₀ h₀ t hused⟩

theorem Lemma4_4_holds : Lemma4_4 := by
  intro State Action instS instA M π η T V₀ h₀ hη k hk hkT
  exact tdSquaredIterateEnergy M π η T V₀ h₀ hη k hk hkT

theorem Lemma4_5_holds : Lemma4_5 := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _, hc₃, h⟩ :=
    tdSource_varianceProxy_exists_universal_constants
  exact ⟨c₁, c₂, c₃, hc₂, horder, hc₃, h⟩

theorem Lemma4_8_holds : Lemma4_8 := by
  intro State Action instS instA M η samples Q₀ t h₀ hη
  have hused : ∀ k, 1 ≤ k → k ≤ t → 0 ≤ η k ∧ η k ≤ 1 :=
    fun k _ _ ↦ hη k
  exact ⟨fun s a ↦ qLearningIterate_bounds M η samples Q₀ h₀ t hused s a,
    fun s ↦ qLearningIterate_value_bounds M η samples Q₀ h₀ t hused s,
    qLearningIterate_optimalQ_error_norm_le M η samples Q₀ h₀ t hused⟩

theorem Lemma4_10_holds : Lemma4_10 := by
  constructor
  · intro State instS instN p γ ρ _hγnonneg hγ hρ value hspan
    exact qComparisonFacts_support_source p γ ρ hγ hρ value hspan
  · intro State Action instS instA M M' ρ hρ hr hγ hballs
    exact qComparisonFacts_stability_source M M' ρ hρ hr hγ hballs

theorem Lemma4_11_holds : Lemma4_11 := by
  intro State Action instS instA M ρ hρ
  dsimp only
  intro Q R
  have h := qRobustBellman_contracting M ρ (2 * ρ / (1 - M.discount)) hρ.le
  constructor
  · simpa [dist_eq_norm, DiscountedMDP.coe_discountConstant] using h.1.2.dist_le_mul Q R
  · simpa [dist_eq_norm, DiscountedMDP.coe_discountConstant] using h.2.2.dist_le_mul Q R

theorem Thm4_6_holds : Thm4_6 := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, _, hc₃, h⟩ :=
    qLearning_exists_universal_constants_source_accuracy
  exact ⟨c₁, c₂, c₃, hc₂, horder, hc₃, h⟩
end StatisticalRL.Statements.Ch4
