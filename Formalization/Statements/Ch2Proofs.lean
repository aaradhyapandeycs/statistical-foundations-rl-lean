import Formalization.Probability.BernoulliKLComparison
import Formalization.Generative.GenerativeLowerBoundBernoulli
import Formalization.Probability.BernoulliTailProofs
import Formalization.MDP.PolicyIteration
import Formalization.MDP.PolicyMatrixResolvent
import Formalization.Probability.AzumaNaturalHistory
import Formalization.Statements.Ch2
import Formalization.Probability.Variance
import Formalization.Probability.FreedmanNaturalHistory

namespace StatisticalRL.Statements
open MeasureTheory

theorem Lemma2_2_holds : Lemma2_2 := by
  intro State Action _ _ M V Vhat hV hVhat
  exact M.transitionVariance_perturbation hV hVhat

theorem Lemma2_9_holds : Lemma2_9 := by
  intro Ω _ μ _ X hX B σ hb hc n K hK hcap δ hδ hδ1
  have hbounded : ∀ᵐ ω ∂μ, |X 0 ω| ≤ B := Filter.Eventually.of_forall (hb 0)
  obtain ⟨ω, hω⟩ := hbounded.exists
  have hB : 0 ≤ B := (abs_nonneg (X 0 ω)).trans hω
  exact freedman_natural_history μ X hX B (σ ^ 2) hB (sq_nonneg σ)
    (fun k ↦ Filter.Eventually.of_forall (hb k)) hc n K hK
    (Filter.Eventually.of_forall hcap) δ hδ hδ1

theorem Lemma2_8_holds : Lemma2_8 := by
  intro Ω _ μ _ X B hX hb hc n δ hδ hδ1
  exact azuma_natural_history_source μ X B hX hb hc n δ hδ hδ1

theorem Lemma2_3_holds : Lemma2_3 := by
  intro State Action _ _ M π
  classical
  rcases M.policyMatrices_resolvent_properties π with
    ⟨⟨_, hP⟩, ⟨_, hQ⟩⟩
  simpa only [DiscountedMDP.policyStateTransitionMatrix,
    DiscountedMDP.policyStateActionTransitionMatrix] using And.intro hP hQ

theorem Lemma2_1_holds : Lemma2_1 := by
  intro State Action _ _ M
  constructor
  · intro Q₀ k _
    exact M.value_iteration_error Q₀ k
  · intro π f hupdate hmax k _
    exact M.arbitraryGreedyPolicyIteration_error π f hupdate hmax k

theorem Lemma2_7_holds.{w} : Lemma2_7.{w} :=
  StatisticalRL.Probability.bernoulliTailBound_source.{w}

theorem Lemma2_13_holds : Lemma2_13 := by
  refine ⟨fun p q hp hp1 hq hq1 => ?_, fun p q hq hqp hp1 => ⟨?_, ?_⟩⟩
  · exact StatisticalRL.GenerativeLowerBound.bernoulliKLExpression_le_quadratic p q hq hq1 hp hp1
  · exact StatisticalRL.Probability.bernoulliKL_le_reverse p q hq hqp hp1
  · have h := StatisticalRL.GenerativeLowerBound.bernoulliKLExpression_le_quadratic q p
      (by linarith) hp1 (by linarith) (by linarith)
    have hsq : (q - p) ^ 2 = (p - q) ^ 2 := by ring
    rw [hsq] at h
    exact h

end StatisticalRL.Statements
