import Formalization.Online.QLearning.OptimalSuffixRange

/-! Actual optimal-value weighted stack concentration, simultaneous in rows
and deterministic prefix lengths; trajectory identification is separate. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningOptimalStackStateMeasurable : MeasurableSpace State := ⊤

theorem qLearning_actualOptimalStack_rate_union
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ < (onlineMDPInitialStackLaw E ρ K).real {sample |
      ∀ (r : OnlineMDPRow State Action H) (j : Fin K),
      |∑ i : Fin (j.val+1), onlineQRateWeight H (j.val+1) (i.val+1) *
        (onlineMDPSuccessorRowLaw E r).centeredSample (qLearningTrueOptimalNext E r) (j.val+1) i
          (onlineStackRowPrefix K (j.val+1) (Nat.succ_le_of_lt j.isLt) r sample.2)| ≤
      Real.sqrt ((H:ℝ)^3/((j.val+1):ℝ)*
        Real.log (4*(Fintype.card (OnlineMDPRow State Action H):ℝ)*(K:ℝ)/δ))} := by
  exact qLearning_actualStack_rate_union H K hH hK E ρ
    (qLearningTrueOptimalNext E) (qLearningTrueOptimalNext_mem_Icc E) δ hδ hδ1
end StatisticalRL.OnlineRL
