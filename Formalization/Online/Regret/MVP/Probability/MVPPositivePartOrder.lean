import Formalization.Online.Regret.MVP.Probability.MVPCorrectedSourceUniformAllK

/-! The untruncated sum is bounded by its positive-part sum. -/
namespace StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvp_batchError_sum_le_positiveParts {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K : ℕ) (l : mvpUniformLevel K) (data : Samples State Action H K)
    (X : Fin H → State → Action → State → ℝ) :
    (∑ h : Fin H, ∑ s : State, ∑ a : Action,
      ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
        (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l)
          (mvpUniformBatchSize_fits_of_level l) j))).expectation (X h s a) -
        ((E h).transition s a).expectation (X h s a))) ≤
    (∑ h : Fin H, ∑ s : State, ∑ a : Action,
      max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
        (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l)
          (mvpUniformBatchSize_fits_of_level l) j))).expectation (X h s a) -
        ((E h).transition s a).expectation (X h s a)) 0) := by
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro a _
  exact le_max_left _ _
end StatisticalRL.FiniteHorizonGenerative
