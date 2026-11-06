import Formalization.Online.QLearning.RateConfidence
import Formalization.Online.QLearning.ActualStackWeightedTail

/-! Actual reset-stack law, fixed row and deterministic positive count. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningRateStackStateMeasurable : MeasurableSpace State := ⊤

theorem qLearning_actualStack_rate_confidence
    (H K n : ℕ) (hH : 0 < H) (hn : 0 < n) (hnK : n ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (r : OnlineMDPRow State Action H) (V : State → ℝ)
    (hV : ∀ s, V s ∈ Set.Icc 0 (H:ℝ)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ < (onlineMDPInitialStackLaw E ρ K).real {sample |
      |∑ i : Fin n, onlineQRateWeight H n (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample V n i
          (onlineStackRowPrefix K n hnK r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/(n:ℝ)*Real.log (2/δ))} := by
  classical
  let good : Set (Fin n → State) := {ω |
    |∑ i : Fin n, onlineQRateWeight H n (i.val+1) *
      (onlineMDPSuccessorRowLaw E r).centeredSample V n i ω| ≤
      Real.sqrt ((H:ℝ)^3/(n:ℝ)*Real.log (2/δ))}
  let A := (onlineStackRowPrefix K n hnK r) ⁻¹' good
  have hmap : (onlineMDPStackLaw E K).real A =
      ((onlineMDPSuccessorRowLaw E r).sampleMeasure n).real good := by
    dsimp [onlineMDPStackLaw, A]
    rw [measureReal_def, ← Measure.map_apply (measurable_of_countable _)
      ((Set.to_countable good).measurableSet), onlineStackRowPrefix_map_law]
    rfl
  have hlift : (onlineMDPInitialStackLaw E ρ K).real (Set.univ ×ˢ A) =
      (onlineMDPStackLaw E K).real A := by
    dsimp [onlineMDPInitialStackLaw]
    rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    rfl
  have hevent : {sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) |
      |∑ i : Fin n, onlineQRateWeight H n (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample V n i
          (onlineStackRowPrefix K n hnK r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/(n:ℝ)*Real.log (2/δ))} = Set.univ ×ˢ A := by
    ext sample
    simp [A,good]
  rw [hevent, hlift, hmap]
  exact qLearning_fixedRow_rate_confidence (onlineMDPSuccessorRowLaw E r) V H n hH hn hV δ hδ hδ1
end StatisticalRL.OnlineRL
