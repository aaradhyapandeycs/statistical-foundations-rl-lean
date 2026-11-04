import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar absorption for corrected MVP T5. -/
namespace StatisticalRL.OnlineRL

theorem mvpT5_radius_absorption
    (H K V q I T2 W3 T8 T5 : ℝ)
    (hH : 0 ≤ H) (hK : 1 ≤ K) (hV : 0 ≤ V) (hq : 1 ≤ q)
    (hi1 : 64*q ≤ I) (hi2 : 2 + 10*q ≤ I)
    (hdet : T5 ≤ W3 + T8 + 2*H*T2 + 2*K*H^2)
    (htail : T8 ≤ Real.sqrt (64*H^2*V*q) + 10*H^2*q) :
    T5 ≤ W3 + 2*H*T2 + Real.sqrt (H^2*V*I) + K*H^2*I := by
  have hmul := mul_le_mul_of_nonneg_left hi1 (show 0 ≤ H^2*V by positivity)
  have hroot : Real.sqrt (64*H^2*V*q) ≤ Real.sqrt (H^2*V*I) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have h1 : 0 ≤ (K-1)*q := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ H^2*(K*I-2*K-10*q) := by
    apply mul_nonneg (sq_nonneg H)
    nlinarith
  linarith
end StatisticalRL.OnlineRL
