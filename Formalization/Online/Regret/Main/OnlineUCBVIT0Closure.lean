import Formalization.Online.Regret.Main.OnlineUCBVISharpT2

/-! Scalar source T0 closure. All T5/T6/T2 component inequalities are visible
hypotheses; connecting them to actual events is a separate obligation. -/
namespace StatisticalRL.OnlineRL

private theorem onlineUCBVI_Lbudget_helper (S A H I L : ℝ)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) (hLI : L ≤ I) (hL : 0 ≤ L) :
    H^2 * L ≤ S^2 * A * H^3 * I := by
  have hs2 : 1 ≤ S^2 := by nlinarith only [hS, sq_nonneg (S - 1)]
  have hfactor : 1 ≤ S^2 * A * H := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ S^2 * A * H := by gcongr
  have hm := mul_le_mul hfactor hLI hL (by positivity : 0 ≤ S^2 * A * H)
  calc
    H^2 * L = (1 * L) * H^2 := by ring
    _ ≤ (S^2 * A * H * I) * H^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg H)
    _ = S^2 * A * H^3 * I := by ring

theorem onlineUCBVI_T0_source_closure
    (S A H K I L V D T5 T2 T0 : ℝ)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hI : 1 ≤ I) (hL : 0 ≤ L) (hLI : L ≤ I) (hD : 0 ≤ D)
    (hV : V ≤ 2 * K * H^2)
    (h5 : T5 ≤ 6 * K * H^2 + (1 / 2 : ℝ) * Real.sqrt (S^2 * A * H^3 * D * I) + 4 * S^2 * A * H^3 * I)
    (h2 : T2 ≤ (1 / 2 : ℝ) * Real.sqrt (S * A * H * T5 * I) + (1 / 2 : ℝ) * S * A * H^2 * I)
    (h0 : T0 ≤ (3 / 8 : ℝ) * Real.sqrt (S * A * H * V * I) +
      (3 / 8 : ℝ) * Real.sqrt (S^2 * A * H * D * I) +
      (1 / 4 : ℝ) * S^2 * A * H^2 * I + 7 * Real.sqrt (K * H^2) * L + T2)
    (hDbound : D ≤ 2 * H^2 * T0 + 18 * H^2 * L) :
    T0 ≤ 20 * Real.sqrt (S * A * H^3 * K) * I + 15 * S^2 * A * H^3 * I := by
  let R := Real.sqrt (S * A * H^3 * K) * I
  let B := S^2 * A * H^3 * I
  let F := A * H^2 * I
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have h2pen := onlineUCBVI_T2_penultimate S A H K I D T5 T2 hS (by linarith)
    (by linarith) (by linarith) (by linarith) hD h5 h2
  have hmass := onlineUCBVI_mass_coeff S F hS hF
  have hsmallD : Real.sqrt (A * H * D * I) ≤ Real.sqrt (S^2 * A * H * D * I) := by
    apply Real.sqrt_le_sqrt
    have hs : 1 ≤ S^2 := by nlinarith [sq_nonneg (S - 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ A * H * D * I by positivity)]
  have hRbase : 0 ≤ S * A * H^3 * K := by positivity
  have hlowroot : Real.sqrt (S * A * H * V * I) ≤ 2 * R := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hr := Real.sq_sqrt hRbase
      have hprod := mul_le_mul_of_nonneg_left hV (show 0 ≤ S * A * H * I by positivity)
      dsimp [R]
      nlinarith [sq_nonneg (I - 1), mul_nonneg (sub_nonneg.mpr hI) hRbase]
  have hT2root : Real.sqrt (6 * S * A * H^3 * K * I) ≤ 3 * R := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hr := Real.sq_sqrt hRbase
      dsimp [R]
      nlinarith [sq_nonneg (I - 1), mul_nonneg (sub_nonneg.mpr hI) hRbase]
  have hnoiseRoot : Real.sqrt (K * H^2) ≤ Real.sqrt (S * A * H^3 * K) := by
    apply Real.sqrt_le_sqrt
    have hSAH : 1 ≤ S * A * H := by
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ S * A * H := by gcongr
    calc
      K * H^2 = 1 * (K * H^2) := by ring
      _ ≤ (S * A * H) * (K * H^2) :=
        mul_le_mul_of_nonneg_right hSAH (by positivity)
      _ = S * A * H^3 * K := by ring
  have hnoise : Real.sqrt (K * H^2) * L ≤ R := by
    dsimp [R]
    calc
      _ ≤ Real.sqrt (S * A * H^3 * K) * L := mul_le_mul_of_nonneg_right hnoiseRoot hL
      _ ≤ _ := mul_le_mul_of_nonneg_left hLI (Real.sqrt_nonneg _)
  have hinter : T0 ≤ 10 * R + Real.sqrt ((B / H^2) * D) + 2 * (B / H) := by
    have hBD : B / H^2 = S^2 * A * H * I := by dsimp [B]; field_simp
    have hBF : B / H = S^2 * F := by dsimp [B, F]; field_simp
    rw [hBD, hBF]
    dsimp [F] at hmass h2pen ⊢
    have hroot : Real.sqrt (S^2 * A * H * I * D) = Real.sqrt (S^2 * A * H * D * I) := by congr 1 <;> ring
    rw [hroot]
    have hDbig := Real.sqrt_nonneg (S^2 * A * H * D * I)
    have hmassNonneg : 0 ≤ S^2 * A * H^2 * I := by positivity
    nlinarith only [h0, h2pen, hmass, hsmallD, hlowroot, hT2root, hnoise, hR, hDbig, hmassNonneg]
  have hLbudget : H^2 * L ≤ B := by
    dsimp [B]
    exact onlineUCBVI_Lbudget_helper S A H I L hS hA hH hLI hL
  have hf := onlineUCBVI_T0_self_bound H R B L T0 D hH hR hB hL hD hLbudget hinter hDbound
  dsimp [R, B] at hf
  simpa only [mul_assoc] using hf
end StatisticalRL.OnlineRL
