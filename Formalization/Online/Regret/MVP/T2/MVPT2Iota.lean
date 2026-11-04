import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation
import Formalization.Online.Regret.W1.OnlineUCBVISourceIota

/-! Fixed-constant source-iota conditions for MVP T2. -/
namespace StatisticalRL.OnlineRL

theorem mvpT2_fixed_iota_conditions (S A H K : ℕ) (δ : ℝ)
    (hS : 0 < S) (hA : 0 < A) (hH : 0 < H) (hK : 2 ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let δp := onlineSourceOptimismDeltaPrime δ S A H K
    let B := Real.log K / Real.log 2
    let L := Real.log (1 / δp)
    let I := onlineW1SourceIota S A H K δp
    16 * (4 : ℝ)^2 * B * L ≤ I ∧ 8 * B * (1 + 16 * L) ≤ I := by
  have hd := mvp_correctedAllocation_domain_and_log δ S A H K hδ hδ1 hS hA hH (by omega)
  have hi := onlineUCBVI_iota_ge_20000_log2_mul_log S A H K
    (onlineSourceOptimismDeltaPrime δ S A H K) hS hA hH hK hd.1 hd.2.1
  have hb : 0 ≤ Real.log K / Real.log 2 := by
    apply div_nonneg (Real.log_nonneg ?_) (le_of_lt (Real.log_pos (by norm_num)))
    exact_mod_cast (show 1 ≤ K by omega)
  have hmul := mul_le_mul_of_nonneg_left hd.2.2 hb
  constructor <;> dsimp <;> nlinarith
end StatisticalRL.OnlineRL
