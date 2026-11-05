import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation
import Formalization.Online.Regret.W1.OnlineUCBVISourceIota
import Formalization.Online.Regret.T3.OnlineRegretT3SourceBound

/-! Logarithmic comparisons for the corrected joint MVP T234 confidence allocation. -/
namespace StatisticalRL.OnlineRL

theorem mvpJoint_log2_KH_le_Hplus_log2K (K H : ℕ) (hK : 2 ≤ K) (hH : 0 < H) :
    (Nat.log2 (K*H) : ℝ) ≤ ((H : ℝ)+1) * (Real.log K / Real.log 2) := by
  let j := Nat.log2 (K*H)
  have hN : 2 ≤ K*H := by nlinarith
  have hNnz : K*H ≠ 0 := by omega
  have hjpowNat : 2^j ≤ K*H := by
    simpa [j, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hNnz
  have hjpow : (2 : ℝ)^j ≤ (K*H : ℕ) := by exact_mod_cast hjpowNat
  have hp : (H : ℝ) ≤ (2 : ℝ)^H := by exact_mod_cast (Nat.le_of_lt H.lt_two_pow_self)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0<K by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogH := Real.log_le_log (by exact_mod_cast hH) hp
  rw [Real.log_pow] at hlogH
  have hlogN := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^j) hjpow
  rw [Real.log_pow, Nat.cast_mul, Real.log_mul (ne_of_gt hKpos) (by exact_mod_cast (ne_of_gt hH))] at hlogN
  have hB : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlog2).2
  dsimp [j] at *
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ H by positivity) (sub_nonneg.mpr hB)]

theorem mvpJoint_corrected_tail_logs (S A H K : ℕ) (δ : ℝ)
    (hS : 0<S) (hA : 0<A) (hH : 0<H) (hK : 2≤K) (hδ : 0<δ) (hδ1 : δ≤1) :
    let δp := onlineSourceOptimismDeltaPrime δ S A H K
    let q := Real.log (1/δp)
    let I := onlineW1SourceIota S A H K δp
    0 < δp/(H+1) ∧ δp/(H+1) ≤ 1/100 ∧
      Real.log (1/(δp/(H+1))) ≤ 2*q ∧ 16*q ≤ I ∧ 10*q ≤ I := by
  have hd := mvp_correctedAllocation_domain_and_log δ S A H K hδ hδ1 hS hA hH (by omega)
  let d := onlineSourceOptimismDeltaPrime δ S A H K
  let den : ℝ := 100*(S : ℝ)^2*(A : ℝ)^2*(H : ℝ)^2*(K : ℝ)^2
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hden : (H : ℝ)+1 ≤ den := by
    dsimp [den]
    have hsq : (H : ℝ)+1 ≤ 100*(H : ℝ)^2 := by nlinarith
    calc
      _ ≤ 100*(H : ℝ)^2 := hsq
      _ = 100*(1 : ℝ)^2*(1 : ℝ)^2*(H : ℝ)^2*(1 : ℝ)^2 := by ring
      _ ≤ 100*(S : ℝ)^2*(A : ℝ)^2*(H : ℝ)^2*(K : ℝ)^2 := by gcongr
  have hdenpos : 0 < den := lt_of_lt_of_le (by positivity : 0 < (H : ℝ)+1) hden
  have hsmall : d ≤ 1/((H : ℝ)+1) := by
    have h1 : d ≤ 1/den := by
      dsimp [d, onlineSourceOptimismDeltaPrime, den]
      exact div_le_div_of_nonneg_right hδ1 (le_of_lt hdenpos)
    exact h1.trans (one_div_le_one_div_of_le (by positivity) hden)
  have hinv : (H : ℝ)+1 ≤ 1/d := by
    rw [le_div_iff₀ (show 0<d from hd.1)]
    simpa [mul_comm] using (le_div_iff₀ (by positivity : 0<(H : ℝ)+1)).mp hsmall
  have hlogH := Real.log_le_log (by positivity : 0<(H : ℝ)+1) hinv
  have hlog : Real.log (1/(d/((H : ℝ)+1))) = Real.log (1/d) + Real.log ((H : ℝ)+1) := by
    have heq : 1/(d/((H : ℝ)+1)) = (1/d)*((H : ℝ)+1) := by
      field_simp [ne_of_gt (show 0<d from hd.1), show (H : ℝ)+1 ≠ 0 by positivity]
    rw [heq, Real.log_mul (ne_of_gt (one_div_pos.mpr hd.1)) (by positivity)]
  have hi := onlineUCBVI_iota_ge_20000_log2_mul_log S A H K d hS hA hH hK hd.1 hd.2.1
  have hb : (1 : ℝ) ≤ Real.log K / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ)<2) (show (2 : ℝ)≤K by exact_mod_cast hK)
  have hmul := mul_le_mul_of_nonneg_right hb (le_trans (by norm_num) hd.2.2)
  dsimp only
  refine ⟨div_pos hd.1 (by positivity), ?_, ?_, ?_, ?_⟩
  · have : 1 ≤ (H : ℝ)+1 := by linarith
    have := div_le_self (le_of_lt hd.1) this
    linarith [hd.2.1]
  · change Real.log (1/(d/((H : ℝ)+1))) ≤ 2*Real.log (1/d)
    rw [hlog]; linarith
  · nlinarith
  · nlinarith
theorem mvpJoint_halfTail_log (d : ℝ) (hd : 0 < d) (hlog : 1 ≤ Real.log (1/d)) :
    Real.log (1/(d/2)) ≤ 2*Real.log (1/d) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heq : 1/(d/2) = 2*(1/d) := by ring
  rw [heq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (one_div_pos.mpr hd))]
  linarith

end StatisticalRL.OnlineRL
