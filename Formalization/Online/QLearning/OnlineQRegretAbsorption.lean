import Mathlib

/-!
# Regret lower-order absorption (Q-learning Step 6)

With `R = √(H⁵SAKL)`: if `K ≥ H³SAL` then `H²SA ≤ R`, so `x ≤ (C + D) R`; otherwise
`HK ≤ R` and `x ≤ HK ≤ R`. Hence `x ≤ max 1 (C + D) · R`. Includes `K = 0` and `C = D = 0`.
-/

namespace StatisticalRL.OnlineQRegretAlgebraPrivate

theorem regretLowerOrderAbsorption (x H S A K L C D : ℝ)
    (hH : 1 ≤ H) (hS : 1 ≤ S) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (htrivial : x ≤ H * K)
    (hmain : x ≤ C * Real.sqrt (H ^ 5 * S * A * K * L) + D * H ^ 2 * S * A) :
    x ≤ max 1 (C + D) * Real.sqrt (H ^ 5 * S * A * K * L) := by
  set R := Real.sqrt (H ^ 5 * S * A * K * L) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hH0 : 0 ≤ H := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hL0 : 0 ≤ L := by linarith
  by_cases hk : H ^ 3 * S * A * L ≤ K
  · -- large K: the lower-order term is dominated
    have hsq : (H ^ 2 * S * A) ^ 2 ≤ H ^ 5 * S * A * K * L := by
      have h4 : 1 ≤ H ^ 4 := one_le_pow₀ hH
      have hl : 1 ≤ L ^ 2 := one_le_pow₀ hL
      have hp : 0 ≤ H ^ 4 * S ^ 2 * A ^ 2 := by positivity
      have hbase : 0 ≤ H ^ 5 * S * A * L :=
        mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hH0 5) hS0) hA0) hL0
      calc (H ^ 2 * S * A) ^ 2 = H ^ 4 * S ^ 2 * A ^ 2 * 1 := by ring
        _ ≤ H ^ 4 * S ^ 2 * A ^ 2 * (H ^ 4 * L ^ 2) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le h4 hl) hp
        _ = H ^ 5 * S * A * L * (H ^ 3 * S * A * L) := by ring
        _ ≤ H ^ 5 * S * A * L * K := mul_le_mul_of_nonneg_left hk hbase
        _ = H ^ 5 * S * A * K * L := by ring
    have hlow : H ^ 2 * S * A ≤ R := by
      calc H ^ 2 * S * A = Real.sqrt ((H ^ 2 * S * A) ^ 2) :=
            (Real.sqrt_sq (mul_nonneg (mul_nonneg (pow_nonneg hH0 2) hS0) hA0)).symm
        _ ≤ R := Real.sqrt_le_sqrt hsq
    have hDR : D * (H ^ 2 * S * A) ≤ D * R := mul_le_mul_of_nonneg_left hlow hD
    have hmax : (C + D) * R ≤ max 1 (C + D) * R :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hR0
    nlinarith
  · -- small K: the trivial bound HK is dominated
    push_neg at hk
    have hsq : (H * K) ^ 2 ≤ H ^ 5 * S * A * K * L := by
      have hHK : 0 ≤ H ^ 2 * K := mul_nonneg (pow_nonneg hH0 2) hK
      calc (H * K) ^ 2 = H ^ 2 * K * K := by ring
        _ ≤ H ^ 2 * K * (H ^ 3 * S * A * L) := mul_le_mul_of_nonneg_left hk.le hHK
        _ = H ^ 5 * S * A * K * L := by ring
    have hHK : H * K ≤ R := by
      calc H * K = Real.sqrt ((H * K) ^ 2) := (Real.sqrt_sq (mul_nonneg hH0 hK)).symm
        _ ≤ R := Real.sqrt_le_sqrt hsq
    have hmax : 1 * R ≤ max 1 (C + D) * R :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
    linarith
end StatisticalRL.OnlineQRegretAlgebraPrivate
