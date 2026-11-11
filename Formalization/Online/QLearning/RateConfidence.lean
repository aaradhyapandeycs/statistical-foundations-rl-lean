import Formalization.Probability.FiniteDistribution
import Formalization.Online.QLearning.RateProxy
import Formalization.Probability.AzumaStrictTwoSided

/-! Fixed-row deterministic-time source-rate confidence; no random-index claim. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
variable {State : Type*} [Fintype State]
local instance qLearningRateConfidenceStateMeasurable : MeasurableSpace State := ⊤

theorem qLearning_fixedRow_rate_confidence
    (d : FiniteDistribution State) (V : State → ℝ) (H n : ℕ)
    (hH : 0 < H) (hn : 0 < n) (hV : ∀ s, V s ∈ Set.Icc 0 (H:ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ < (d.sampleMeasure n).real {ω |
      |∑ i : Fin n, onlineQRateWeight H n (i.val+1) * d.centeredSample V n i ω| ≤
        Real.sqrt ((H:ℝ)^3/(n:ℝ)*Real.log (2/δ))} := by
  let w : Fin n → ℝ := fun i => onlineQRateWeight H n (i.val+1)
  let X : (Fin n → State) → ℝ := fun ω => ∑ i : Fin n, w i * d.centeredSample V n i ω
  let c : ℝ≥0 := ⟨(H:ℝ)^3/(2*(n:ℝ)), by positivity⟩
  have hc : 0 < c := by
    apply NNReal.coe_pos.mp
    dsimp [c]
    positivity
  have hbase := d.qLearning_weightedRow_subgaussian V n (H:ℝ) hV w
  have hproxy := qLearning_rate_proxy_le H n hH hn
  have hX : HasSubgaussianMGF X c (d.sampleMeasure n) := by
    constructor
    · exact hbase.integrable_exp_mul
    · intro x
      calc
        ProbabilityTheory.mgf X (d.sampleMeasure n) x ≤
            Real.exp (((∑ i : Fin n, ‖w i‖₊^2 * (‖(H:ℝ)‖₊/2)^2 : ℝ≥0) : ℝ)*x^2/2) := hbase.mgf_le x
        _ ≤ Real.exp ((c:ℝ)*x^2/2) := by
          apply Real.exp_le_exp.mpr
          have hs : 0 ≤ x^2 := sq_nonneg x
          dsimp [c,w]
          nlinarith
  have hm : Measurable X := measurable_of_countable _
  have h := StatisticalRL.azuma_subgaussian_strict_two_sided (d.sampleMeasure n) X hm c hc hX δ hδ hδ1
  have he : 2*(c:ℝ) = (H:ℝ)^3/(n:ℝ) := by dsimp [c]; ring
  simpa [X,w,he] using h
end StatisticalRL.OnlineRL
