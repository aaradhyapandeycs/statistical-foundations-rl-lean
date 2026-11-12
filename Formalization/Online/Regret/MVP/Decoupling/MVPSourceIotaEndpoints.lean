import Formalization.Online.Regret.MVP.Decoupling.MVPDyadicSlotSums
import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! source-parameter endpoints for the decoupling aggregation. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_sourceIota_ge_20000 (d K : ℕ) (δp : ℝ)
    (hd : 1 ≤ d) (hK : 2 ≤ K) (hδ : 0 < δp) (hδsmall : δp ≤ 1/100) :
    20000 ≤ 40000*(Real.log K/Real.log 2)^3*Real.log (3*d)*Real.log (1/δp) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ Real.log K/Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2
    simpa using Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ K by exact_mod_cast hK)
  have hz : (1/2:ℝ) ≤ Real.log (3*d) := by
    have hb : (2:ℝ) ≤ 3*(d:ℝ) := by nlinarith only [hd1]
    have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hb
    norm_num at h1
    linarith only [h1,h2]
  have hq := onlineSmallConfidence_log_ge_one δp hδ hδsmall
  calc
    20000 = 40000*(1:ℝ)^3*(1/2)*1 := by norm_num
    _ ≤ 40000*(Real.log K/Real.log 2)^3*Real.log (3*d)*Real.log (1/δp) := by
      gcongr

theorem mvp_sum_sourceDyadicSlots_zeroExtended (K : ℕ)
    (f : ℕ → ℝ) (hzero : ∀ u, K ≤ u → f u = 0) :
    (∑ u ∈ Finset.range K, f u) =
      f 0 + f 1 + ∑ j ∈ Finset.range (Nat.log2 K),
        ∑ i ∈ Finset.range (2*2^j), f (2*2^j+i) := by
  exact mvp_sum_dyadicSlots_zeroExtended K _
    (onlineMVP_lt_nextFloorPower K).le f hzero

end StatisticalRL.OnlineRL
