import Formalization.Online.QLearning.WeightedRowTail
import Formalization.Online.SourceOptimism.StackPrefixMarginal
import Formalization.Online.SourceOptimism.EpisodicStackSelector

/-! Fixed row and deterministic prefix only; no claim about a random count. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningActualWeightedStateMeasurable : MeasurableSpace State := ⊤

/-- Lift the fixed deterministic weighted-row tail to the actual independent
reset-vector and successor-stack law. -/
theorem qLearning_actualStack_weightedRow_twoSided
    (H K n : ℕ) (hn : n ≤ K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (r : OnlineMDPRow State Action H)
    (V : State → ℝ) (B t : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (w : Fin n → ℝ) (ht : 0 ≤ t) :
    (onlineMDPInitialStackLaw E ρ K).real
      {sample | t ≤ |∑ i : Fin n, w i *
        (onlineMDPSuccessorRowLaw E r).centeredSample V n i
          (onlineStackRowPrefix K n hn r sample.2)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((∑ i : Fin n, ‖w i‖₊ ^ 2 * (‖B‖₊ / 2)^2 : ℝ≥0) : ℝ))) := by
  classical
  let good : Set (Fin n → State) := {ω | t ≤ |∑ i : Fin n,
    w i * (onlineMDPSuccessorRowLaw E r).centeredSample V n i ω|}
  let A := (onlineStackRowPrefix K n hn r) ⁻¹' good
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
      t ≤ |∑ i : Fin n, w i * (onlineMDPSuccessorRowLaw E r).centeredSample V n i
        (onlineStackRowPrefix K n hn r sample.2)|} = Set.univ ×ˢ A := by
    ext sample
    simp [A, good]
  rw [hevent, hlift, hmap]
  exact (onlineMDPSuccessorRowLaw E r).qLearning_weightedRow_twoSided V n B t hV w ht
end StatisticalRL.OnlineRL
