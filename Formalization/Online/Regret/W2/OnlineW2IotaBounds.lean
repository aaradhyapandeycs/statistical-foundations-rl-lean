import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.W1.OnlineW1LogBounds

/-! OnlineW2IotaBounds: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL

/-- The displayed source iota dominates the coefficients required for the
coarse W₂ estimate whenever K≥2; δ′ is any positive source-small value. -/
theorem onlineW2SourceIota_bounds
    (S A H K : ℕ) (δ' : ℝ) (hS : 0 < S) (hA : 0 < A) (hH : 0 < H)
    (hK : 2 ≤ K) (hδ : 0 < δ') (hδsmall : δ' ≤ 1 / 100) :
    let L := Real.log (1 / δ')
    let Q := 1 + Real.log (K + 1 : ℝ)
    256 * L * Q ≤ onlineW1SourceIota S A H K δ' ∧
    (16 / 3 : ℝ) * L * Q ≤ onlineW1SourceIota S A H K δ' ∧
    24 ≤ onlineW1SourceIota S A H K δ' := by
  let L := Real.log (1 / δ')
  let Q := 1 + Real.log (K + 1 : ℝ)
  let b := Real.log K / Real.log 2
  let g := Real.log (3 * S * A * H : ℝ)
  let lb := Real.log (1 / δ')
  have hL : 0 ≤ L := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ hδ).2
    linarith
  have hlb : 1 ≤ lb := onlineSmallConfidence_log_ge_one δ' hδ hδsmall
  have hLlb : L ≤ lb := le_rfl
  have hb : 1 ≤ b := by
    dsimp [b]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ K by exact_mod_cast hK)
  have hg : (1 / 2 : ℝ) ≤ g := by
    have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hSAH : (2 : ℝ) ≤ 3 * S * A * H := by
      calc
        (2 : ℝ) ≤ 3 * 1 * 1 * 1 := by norm_num
        _ ≤ 3 * S * A * H := by gcongr
    have hbase := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hSAH
    dsimp [g]
    norm_num at hbase
    linarith
  have hQ : Q ≤ 4 * b := onlineW1_logEnvelope_le K hK
  have hQ0 : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (K + 1 : ℝ) := Real.log_nonneg (by
      have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith)
    dsimp [Q]; linarith
  have hcube : b ≤ b^3 := by nlinarith [sq_nonneg (b-1), sq_nonneg b]
  have hbg : b / 2 ≤ b^3 * g := by
    have h1 := mul_le_mul_of_nonneg_right hcube (show 0 ≤ g by linarith)
    have h2 := mul_le_mul_of_nonneg_left hg (show 0 ≤ b by linarith)
    nlinarith
  have hiota : 20000 * b * lb ≤ onlineW1SourceIota S A H K δ' := by
    have hh := mul_le_mul_of_nonneg_right hbg (show 0 ≤ lb by linarith)
    dsimp [onlineW1SourceIota]
    change 20000 * b * lb ≤ 40000 * b^3 * g * lb
    nlinarith
  have hprod : L * Q ≤ lb * (4 * b) := by
    exact mul_le_mul hLlb hQ hQ0 (by linarith : 0 ≤ lb)
  have hprod0 : 0 ≤ L * Q := mul_nonneg hL hQ0
  have hlarge : 256 * L * Q ≤ onlineW1SourceIota S A H K δ' := by
    nlinarith [mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ lb by linarith)]
  have hsmall : (16 / 3 : ℝ) * L * Q ≤ onlineW1SourceIota S A H K δ' := by
    nlinarith
  have h24 : 24 ≤ onlineW1SourceIota S A H K δ' := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hlb)]
  exact ⟨hlarge, hsmall, h24⟩
end StatisticalRL.OnlineRL
