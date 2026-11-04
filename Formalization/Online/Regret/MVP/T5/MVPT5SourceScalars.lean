import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation
import Formalization.Online.Regret.W1.OnlineUCBVISourceIota
import Formalization.Online.Regret.T3.OnlineRegretT3SourceBound

/-! Corrected-allocation logarithmic bounds for MVP T5. -/
namespace StatisticalRL.OnlineRL

theorem mvpT5_corrected_iota_and_tail_bounds (S A H K : ℕ) (δ : ℝ)
    (hS : 0 < S) (hA : 0 < A) (hH : 0 < H) (hK : 2 ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let δp := onlineSourceOptimismDeltaPrime δ S A H K
    let q := Real.log (1/δp)
    let I := onlineW1SourceIota S A H K δp
    64*q ≤ I ∧ 2 + 10*q ≤ I ∧ Real.log (1/(δp/2)) ≤ 2*q := by
  have hd := mvp_correctedAllocation_domain_and_log δ S A H K hδ hδ1 hS hA hH (by omega)
  have hi := onlineUCBVI_iota_ge_20000_log2_mul_log S A H K
    (onlineSourceOptimismDeltaPrime δ S A H K) hS hA hH hK hd.1 hd.2.1
  have hb : (1 : ℝ) ≤ Real.log K / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ K by exact_mod_cast hK)
  have hmul := mul_le_mul_of_nonneg_right hb (le_trans (by norm_num) hd.2.2)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log (1/(onlineSourceOptimismDeltaPrime δ S A H K/2)) =
      Real.log 2 + Real.log (1/onlineSourceOptimismDeltaPrime δ S A H K) := by
    have heq : 1/(onlineSourceOptimismDeltaPrime δ S A H K/2) =
        2*(1/onlineSourceOptimismDeltaPrime δ S A H K) := by ring
    rw [heq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (one_div_pos.mpr hd.1))]
  dsimp only
  rw [hlog]
  constructor
  · nlinarith
  constructor <;> nlinarith [hd.2.2]

theorem mvpT5_log2_count_le_two_log (N : ℕ) (hN : 2 ≤ N) :
    (Nat.log2 N : ℝ) ≤ 2*Real.log N := by
  let j := Nat.log2 N
  have hp : (2 : ℝ)^j ≤ N := by
    exact_mod_cast (show 2^j ≤ N by simpa [j, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (by omega : N ≠ 0))
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^j) hp
  rw [Real.log_pow] at hl
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hj : (0 : ℝ) ≤ j := by positivity
  have hm := mul_le_mul_of_nonneg_left hlog2 hj
  dsimp [j] at *
  nlinarith
end StatisticalRL.OnlineRL
