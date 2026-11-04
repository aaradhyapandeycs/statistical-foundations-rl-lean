import Formalization.Online.Regret.MVP.Probability.MVPActualBatchIncrement

/-! Fixed-mask aggregate batch Bernstein-Freedman bound on the actual product law. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_actualBatchFixedMask_freedman {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K n : ℕ) (hn : 2*n ≤ K) (hnpos : 0<n) (mask : Fin H → State → Action → Bool)
    (V : (h : Fin H) → State → Action → FutureCode (State := State) (Action := Action) h K → State → ℝ)
    (hV : ∀ h s a code x, 0 ≤ V h s a code x ∧ V h s a code x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (samplingLaw E K).real {data |
      |∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then
          (FiniteDistribution.empiricalRow n hnpos (fun j => data ((h,s,a),mvpBatchIndex K n hn j))).expectation
              (V h s a (futureData h K data)) -
            ((E h).transition s a).expectation (V h s a (futureData h K data))
        else 0| ≤
      (Real.sqrt (8 * max
          ((n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            if mask h s a then ((E h).transition s a).variance (V h s a (futureData h K data)) else 0)
          (((n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / δ)) + (4/3) * H * Real.log (2 * peels / δ)) / n} := by
  let μ := samplingLaw E K
  let M := H * Fintype.card (State × Action × Fin K)
  let order := mvpExpandedOrder (State := State) (Action := Action) H K
  let d := fun i : SampleIndex State Action H K => (E i.1.1).transition i.1.2.1 i.1.2.2
  let X := mvpPaddedRevealIncrement order d (mvpActualPredictableTest H K n mask V)
  let σ₂ : ℝ := (n : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2
  let A : Set (Samples State Action H K) := {data |
    |StatisticalRL.incrementSum X M data| ≤ Real.sqrt (8 * max
      (StatisticalRL.predictableSecondMomentSum μ (mvpRevealFiltration (Outcome := State) order) X M data)
      (σ₂ / (2 : ℝ)^peels) * Real.log (2 * peels / δ)) + (4/3) * H * Real.log (2 * peels / δ)}
  let B : Set (Samples State Action H K) := {data |
      |∑ h : Fin H, ∑ s : State, ∑ a : Action,
        if mask h s a then
          (FiniteDistribution.empiricalRow n hnpos (fun j => data ((h,s,a),mvpBatchIndex K n hn j))).expectation
              (V h s a (futureData h K data)) -
            ((E h).transition s a).expectation (V h s a (futureData h K data))
        else 0| ≤
      (Real.sqrt (8 * max
          ((n : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            if mask h s a then ((E h).transition s a).variance (V h s a (futureData h K data)) else 0)
          (σ₂ / (2 : ℝ)^peels) * Real.log (2 * peels / δ)) + (4/3) * H * Real.log (2 * peels / δ)) / n}
  have hA : 1 - δ ≤ μ.real A :=
    mvp_actualFixedMask_sharpFreedman E K n hn mask V hV peels hp δ hδ hδ1
  have hsub : A ≤ᵐ[μ] B := by
    filter_upwards [mvp_actualPredictableVariance_eq_batchRows E K n hn mask V] with data hv ha
    have hi := mvp_actualIncrementSum_eq_batchErrors E K n hn hnpos mask V data
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    change |StatisticalRL.incrementSum X M data| ≤ _ at ha
    change |∑ h : Fin H, ∑ s : State, ∑ a : Action, if mask h s a then _ else 0| ≤ _
    rw [hi, abs_mul, abs_of_pos hnreal, hv] at ha
    exact (le_div_iff₀ hnreal).2 (by nlinarith)
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  exact hA.trans hm
end StatisticalRL.FiniteHorizonGenerative
