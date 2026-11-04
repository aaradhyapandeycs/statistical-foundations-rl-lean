import Formalization.Online.Regret.MVP.Probability.MVPBatchIndex
import Formalization.Probability.EmpiricalRow

/-! Exact joint product law of a deterministic contiguous batch. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

variable {State : Type*} [Fintype State]
local instance mvpBatchLawStateMeasurable : MeasurableSpace State := ⊤

def mvpBatchSlice (K n : ℕ) (h : 2*n ≤ K) (ω : Fin K → State) : Fin n → State :=
  fun i => ω (mvpBatchIndex K n h i)

theorem mvpBatchSlice_law (d : FiniteDistribution State) (K n : ℕ) (h : 2*n ≤ K) :
    (d.sampleMeasure K).map (mvpBatchSlice K n h) = d.sampleMeasure n := by
  have hi := (d.sampleMeasure_independent K).precomp (mvpBatchIndex_injective K n h)
  have hm : ∀ i : Fin n, AEMeasurable (fun ω : Fin K → State => ω (mvpBatchIndex K n h i))
      (d.sampleMeasure K) := fun i => (measurable_pi_apply _).aemeasurable
  have hh := (iIndepFun_iff_map_fun_eq_pi_map hm).1 hi
  have hcoord : (fun i : Fin n => (d.sampleMeasure K).map
      (fun ω : Fin K → State => ω (mvpBatchIndex K n h i))) =
      (fun _ : Fin n => d.rowMeasure) := by
    funext i
    exact d.sampleMeasure_coordinate K _
  rw [hcoord] at hh
  exact hh
end StatisticalRL.OnlineRL
