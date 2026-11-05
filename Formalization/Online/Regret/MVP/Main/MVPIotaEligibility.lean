import Formalization.Online.Regret.MVP.T2.MVPT2Iota

/-! The large proof branch supplies the source level-range requirement. -/
namespace StatisticalRL.OnlineRL

theorem mvp_main_iota_ge_log2 (S A H K : ℕ) (δ : ℝ)
    (hS : 0<S) (hA : 0<A) (hH : 0<H) (hK : 2≤K)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    Real.log K / Real.log 2 ≤
      onlineW1SourceIota S A H K (onlineSourceOptimismDeltaPrime δ S A H K) := by
  have hd := mvp_correctedAllocation_domain_and_log δ S A H K hδ hδ1 hS hA hH (by omega)
  have hi := onlineUCBVI_iota_ge_20000_log2_mul_log S A H K
    (onlineSourceOptimismDeltaPrime δ S A H K) hS hA hH hK hd.1 hd.2.1
  have hb : 0≤Real.log K / Real.log 2 := by
    apply div_nonneg (Real.log_nonneg ?_) (le_of_lt (Real.log_pos (by norm_num)))
    exact_mod_cast (show 1≤K by omega)
  have hmul := mul_le_mul_of_nonneg_left hd.2.2 hb
  nlinarith
end StatisticalRL.OnlineRL
