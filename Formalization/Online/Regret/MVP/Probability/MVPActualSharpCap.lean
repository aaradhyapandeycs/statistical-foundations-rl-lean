import Formalization.Online.Regret.MVP.Probability.MVPActualVarianceExact

/-! Exact batch-size variance cap for actual expanded samples. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualPredictableVariance_le_batchCap {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K n : ℕ) (hn : 2*n ≤ K)
    (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ h s a code x, 0 ≤ V h s a code x ∧ V h s a code x ≤ H) :
    let order := mvpExpandedOrder (State := State) (Action := Action) H K
    let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
    let F := mvpActualPredictableTest H K n mask V
    ∀ᵐ data ∂(samplingLaw E K),
      StatisticalRL.predictableSecondMomentSum (samplingLaw E K)
        (mvpRevealFiltration (Outcome := State) order) (mvpPaddedRevealIncrement order d F)
          (H * Fintype.card (State × Action × Fin K)) data ≤
      (n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2 := by
  classical
  filter_upwards [mvp_actualPredictableVariance_eq_batchRows E K n hn mask V] with data heq
  rw [heq]
  have hsum : (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then ((E h).transition s a).variance (V h s a (futureData h K data)) else 0)
      ≤ (H : ℝ) * Fintype.card State * Fintype.card Action * (H : ℝ)^2 := by
    calc
      _ ≤ ∑ _h : Fin H, ∑ _s : State, ∑ _a : Action, (H : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro h _
        apply Finset.sum_le_sum
        intro s _
        apply Finset.sum_le_sum
        intro a _
        split
        · calc
            _ ≤ ((E h).transition s a).expectation (fun x => (V h s a (futureData h K data) x)^2) :=
              ((E h).transition s a).variance_le_expectation_sq _
            _ ≤ (H : ℝ)^2 := by
              apply ((E h).transition s a).expectation_le_const
              intro x
              have hx := hV h s a (futureData h K data) x
              nlinarith
        · positivity
      _ = _ := by simp; ring
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
end StatisticalRL.FiniteHorizonGenerative
