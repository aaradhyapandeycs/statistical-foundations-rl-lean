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

end StatisticalRL.Statements
