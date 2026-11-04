import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Confidence arithmetic for the joint source T2/T3/T4 event. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory

theorem onlineTwoEvent_confidence_strict
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) (a b : ℝ)
    (hA : 1 - a ≤ μ.real A) (hB : 1 - b < μ.real B) :
    1 - (a + b) < μ.real (A ∩ B) := by
  have hAcomp := measureReal_compl (μ := μ) ((Set.to_countable A).measurableSet)
  have hBcomp := measureReal_compl (μ := μ) ((Set.to_countable B).measurableSet)
  have hIcomp := measureReal_compl (μ := μ) ((Set.to_countable (A ∩ B)).measurableSet)
  rw [probReal_univ] at hAcomp hBcomp hIcomp
  have hu := measureReal_union_le (μ := μ) Aᶜ Bᶜ
  have he : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := Set.compl_inter A B
  rw [he] at hIcomp
  linarith

theorem onlineT234_failureCoefficient_le_source
    (N : ℕ) (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 ≤ δ) :
    2 * (Nat.log2 N : ℝ) * δ + 2 * δ ≤
      4 * (Real.log N / Real.log 2) * δ := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor : (Nat.log2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa only [Real.logb] using Real.log2_le_logb N
  have hlogone : 1 ≤ Real.log N / Real.log 2 := by
    apply (le_div_iff₀ hlogtwo).mpr
    simpa only [one_mul] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hscalar : 2 * (Nat.log2 N : ℝ) + 2 ≤ 4 * (Real.log N / Real.log 2) := by
    linarith
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hscalar hδ

end StatisticalRL.OnlineRL
