import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.OnlineZeroCountOptimisticUpdate

/-! Corrected reciprocal confidence allocation for the MVP analysis. -/
namespace StatisticalRL.OnlineRL

theorem mvp_correctedAllocation_domain_and_log (δ : ℝ) (S A H K : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : 0 < S) (hA : 0 < A) (hH : 0 < H) (hK : 0 < K) :
    0 < onlineSourceOptimismDeltaPrime δ S A H K ∧
      onlineSourceOptimismDeltaPrime δ S A H K ≤ 1/100 ∧
      1 ≤ Real.log (1 / onlineSourceOptimismDeltaPrime δ S A H K) := by
  have hd := onlineSourceOptimismDeltaPrime_domain δ S A H K hδ hδ1 hS hA hH hK
  exact ⟨hd.1, hd.2, onlineSmallConfidence_log_ge_one _ hd.1 hd.2⟩
end StatisticalRL.OnlineRL
