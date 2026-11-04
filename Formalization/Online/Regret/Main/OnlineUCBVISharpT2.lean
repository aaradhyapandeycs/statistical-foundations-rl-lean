import Formalization.Online.Regret.Main.OnlineUCBVIScalar

/-! Sharp combined Young step for the source T2 penultimate bound. The
hypotheses here are scalar component estimates, not an actual-event result. -/
namespace StatisticalRL.OnlineRL

/-- Combining the nested and linear T5 terms before Young preserves the
source's 1/4 coefficient on S²F. -/
theorem onlineUCBVI_sharp_combined_root (S F X : ℝ)
    (hS : 1 ≤ S) (hF : 0 ≤ F) (hX : 0 ≤ X) :
    (1 / 2 : ℝ) * Real.sqrt (S^2 * F * ((1 / 2 : ℝ) * X + 4 * S * F)) ≤
      (1 / 4 : ℝ) * S^2 * F + (1 / 8 : ℝ) * X + S * F := by
  have ha : 0 ≤ S^2 * F / 2 := by positivity
  have hb : 0 ≤ X / 4 + 2 * S * F := by positivity
  have hy := onlineT56_sqrt_product_young (S^2 * F / 2) (X / 4 + 2 * S * F) ha hb
  have heq : (S^2 * F / 2) * (X / 4 + 2 * S * F) =
      (1 / 4 : ℝ) * (S^2 * F * ((1 / 2 : ℝ) * X + 4 * S * F)) := by ring
  rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hy
  norm_num only [show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by norm_num] at hy
  nlinarith only [hy]

/-- Exact scalar shape of the source's penultimate T2 estimate. -/
theorem onlineUCBVI_T2_penultimate (S A H K I D T5 T2 : ℝ)
    (hS : 1 ≤ S) (hA : 0 ≤ A) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hI : 0 ≤ I) (hD : 0 ≤ D)
    (h5 : T5 ≤ 6 * K * H^2 + (1 / 2 : ℝ) * Real.sqrt (S^2 * A * H^3 * D * I) + 4 * S^2 * A * H^3 * I)
    (h2 : T2 ≤ (1 / 2 : ℝ) * Real.sqrt (S * A * H * T5 * I) +
      (1 / 2 : ℝ) * S * A * H^2 * I) :
    T2 ≤ (1 / 2 : ℝ) * Real.sqrt (6 * S * A * H^3 * K * I) +
      (1 / 8 : ℝ) * Real.sqrt (A * H * D * I) +
      ((1 / 4 : ℝ) * S^2 + (3 / 2 : ℝ) * S) * (A * H^2 * I) := by
  let F := A * H^2 * I
  let X := Real.sqrt (A * H * D * I)
  let a := S * A * H * I
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq : Real.sqrt (S^2 * A * H^3 * D * I) = S * H * X := by
    have hmul : S^2 * A * H^3 * D * I = (S * H)^2 * (A * H * D * I) := by ring
    rw [hmul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ S * H)]
  have hmain : a * (6 * K * H^2) = 6 * S * A * H^3 * K * I := by dsimp [a]; ring
  have hrest : a * ((1 / 2 : ℝ) * (S * H * X) + 4 * S^2 * A * H^3 * I) =
      S^2 * F * ((1 / 2 : ℝ) * X + 4 * S * F) := by dsimp [a, F]; ring
  have hmul := mul_le_mul_of_nonneg_left h5 ha
  rw [hq] at hmul
  have hsqrt := Real.sqrt_le_sqrt hmul
  have hsplit := onlineUCBVI_sqrt_three (6 * S * A * H^3 * K * I)
    (S^2 * F * ((1 / 2 : ℝ) * X + 4 * S * F)) 0
    (by positivity) (by positivity) (by positivity)
  have hsum : a * (6 * K * H^2 + (1 / 2 : ℝ) * (S * H * X) + 4 * S^2 * A * H^3 * I) =
      6 * S * A * H^3 * K * I + S^2 * F * ((1 / 2 : ℝ) * X + 4 * S * F) + 0 := by
    rw [← hmain, ← hrest]
    ring
  rw [hsum] at hsqrt
  simp only [Real.sqrt_zero, add_zero] at hsplit
  have hsharp := onlineUCBVI_sharp_combined_root S F X hS hF hX
  have harg : S * A * H * T5 * I = a * T5 := by dsimp [a]; ring
  rw [harg] at h2
  simp only [add_zero] at hsqrt
  dsimp [F, X] at hsharp hsqrt hsplit ⊢
  linarith only [h2, hsqrt, hsplit, hsharp]
end StatisticalRL.OnlineRL
