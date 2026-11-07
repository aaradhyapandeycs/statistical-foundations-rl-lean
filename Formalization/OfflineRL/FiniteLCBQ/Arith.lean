import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite-horizon LCB-Q: the final constant arithmetic (Step 5 of the plan)

With `c_a = 10⁶ c_b²`, `c_b ≥ 5`, `K ≥ c_a H⁵ S C⋆ L / ε²`, `ε ≤ H`, `L ≥ 0.69` and `ι' ≤ 5L`:
`21 H R / K ≤ ε` where `R = 2HSC⋆ + 8C⋆H²ι' + 16 c_b √(H³L) (√(2KC⋆S) + S C⋆ √ι')`.
-/

namespace StatisticalRL.LCBQFinite

theorem sqrt_bound {X b : ℝ} (hX : 0 ≤ X) (hb : 0 ≤ b) (hsq : X ^ 2 ≤ b ^ 2) : X ≤ b := by
  rw [← Real.sqrt_sq hX, ← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt hsq

theorem final_arith {H S C K L ι' cb ε : ℝ} (hH : 1 ≤ H) (hS : 1 ≤ S) (hC : 1 ≤ C) (hK : 0 < K)
    (hL : 0.69 ≤ L) (hι : ι' ≤ 5 * L) (hcb : 5 ≤ cb) (hε : 0 < ε) (hεH : ε ≤ H)
    (hKc : 10 ^ 6 * cb ^ 2 * H ^ 5 * S * C * L / ε ^ 2 ≤ K) :
    21 * H * (2 * H * S * C + 8 * C * H ^ 2 * ι' +
      16 * (cb * Real.sqrt (H ^ 3 * L)) * (Real.sqrt (2 * K * C * S) + S * C * Real.sqrt ι')) / K
      ≤ ε := by
  set ca := 10 ^ 6 * cb ^ 2 with hca
  have hca0 : 25 * 10 ^ 6 ≤ ca := by simp only [ca]; nlinarith
  have hcap : 0 < ca := by linarith
  have hH0 : 0 < H := by linarith
  have hL0 : 0 < L := by linarith
  have hS0 : 0 < S := by linarith
  have hC0 : 0 < C := by linarith
  have hcb0 : 0 < cb := by linarith
  -- P := ca H⁴ S C L ≤ ε K
  have hK2 : ca * H ^ 5 * S * C * L ≤ K * ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hKc; linarith
  have hP : ca * H ^ 4 * S * C * L ≤ ε * K := by
    have h1 : K * ε ^ 2 ≤ K * ε * H := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_left hεH (by positivity)
    have h2 : (ca * H ^ 4 * S * C * L) * H ≤ (ε * K) * H := by
      calc (ca * H ^ 4 * S * C * L) * H = ca * H ^ 5 * S * C * L := by ring
        _ ≤ K * ε * H := hK2.trans h1
        _ = (ε * K) * H := by ring
    exact le_of_mul_le_mul_right h2 hH0
  set P := ca * H ^ 4 * S * C * L
  have hH2 : H ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH (by norm_num)
  have hH3 : H ^ 3 ≤ H ^ 4 := pow_le_pow_right₀ hH (by norm_num)
  have hH21 : 1 ≤ H ^ 2 := one_le_pow₀ hH
  -- (1)
  have t1 : 42 * H ^ 2 * S * C ≤ 61 / ca * (ε * K) := by
    have a1 : 0.69 * (H ^ 2 * S * C) ≤ H ^ 4 * S * C * L := by
      have : 0.69 * H ^ 2 ≤ H ^ 4 * L := by nlinarith
      have hSC : 0 ≤ S * C := by positivity
      calc 0.69 * (H ^ 2 * S * C) = (0.69 * H ^ 2) * (S * C) := by ring
        _ ≤ (H ^ 4 * L) * (S * C) := mul_le_mul_of_nonneg_right this hSC
        _ = _ := by ring
    have a2 : 42 * H ^ 2 * S * C ≤ 61 / ca * P := by
      simp only [P]
      rw [div_mul_eq_mul_div, le_div_iff₀ hcap]
      have h := mul_le_mul_of_nonneg_left a1 hcap.le
      have hp : 0 ≤ ca * (H ^ 2 * S * C) := by positivity
      linarith
    exact a2.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  -- (2)
  have t2 : 168 * C * H ^ 3 * ι' ≤ 840 / ca * (ε * K) := by
    have a1 : 168 * C * H ^ 3 * ι' ≤ 840 * (H ^ 4 * S * C * L) := by
      have b1 : C * H ^ 3 * ι' ≤ C * H ^ 3 * (5 * L) :=
        mul_le_mul_of_nonneg_left hι (by positivity)
      have b2 : C * H ^ 3 * L ≤ H ^ 4 * S * C * L := by
        have : C * H ^ 3 * L * 1 ≤ C * H ^ 4 * L * S :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH3 hC0.le) hL0.le)
            hS zero_le_one (by positivity)
        linarith
      nlinarith
    have a2 : 840 * (H ^ 4 * S * C * L) = 840 / ca * P := by
      simp only [P]; field_simp
    rw [a2] at a1
    exact a1.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  -- (3)
  have t3 : 336 * H * (cb * Real.sqrt (H ^ 3 * L)) * Real.sqrt (2 * K * C * S) ≤ 0.48 * (ε * K) := by
    have hX : 0 ≤ 336 * H * (cb * Real.sqrt (H ^ 3 * L)) * Real.sqrt (2 * K * C * S) := by positivity
    refine sqrt_bound hX (by positivity) ?_
    have e : (336 * H * (cb * Real.sqrt (H ^ 3 * L)) * Real.sqrt (2 * K * C * S)) ^ 2 =
        2 * 336 ^ 2 * cb ^ 2 * K * (H ^ 5 * S * C * L) := by
      have e1 : (336 * H * (cb * Real.sqrt (H ^ 3 * L)) * Real.sqrt (2 * K * C * S)) ^ 2 =
          336 ^ 2 * H ^ 2 * cb ^ 2 * (Real.sqrt (H ^ 3 * L)) ^ 2 * (Real.sqrt (2 * K * C * S)) ^ 2 := by
        ring
      rw [e1, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring
    rw [e]
    have h5 : H ^ 5 * S * C * L ≤ K * ε ^ 2 / ca := by
      rw [le_div_iff₀ hcap]; linarith
    calc 2 * 336 ^ 2 * cb ^ 2 * K * (H ^ 5 * S * C * L)
        ≤ 2 * 336 ^ 2 * cb ^ 2 * K * (K * ε ^ 2 / ca) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 2 * 336 ^ 2 / 10 ^ 6 * (ε * K) ^ 2 := by simp only [ca]; field_simp
      _ ≤ (0.48 * (ε * K)) ^ 2 := by
          rw [show (0.48 * (ε * K)) ^ 2 = (0.48 : ℝ) ^ 2 * (ε * K) ^ 2 by ring]
          exact mul_le_mul_of_nonneg_right
            (show (2 * 336 ^ 2 / 10 ^ 6 : ℝ) ≤ 0.48 ^ 2 by norm_num) (sq_nonneg _)
  -- (4)
  have t4 : 336 * H * (cb * Real.sqrt (H ^ 3 * L)) * (S * C * Real.sqrt ι') ≤
      1008 * cb / ca * (ε * K) := by
    have hsq : Real.sqrt (H ^ 3 * L) * Real.sqrt ι' ≤ 3 * H ^ 2 * L := by
      rw [← Real.sqrt_mul (by positivity)]
      refine (Real.sqrt_le_sqrt (?_ : H ^ 3 * L * ι' ≤ (3 * H ^ 2 * L) ^ 2)).trans_eq
        (Real.sqrt_sq (by positivity))
      have b1 : H ^ 3 * L * ι' ≤ H ^ 3 * L * (5 * L) :=
        mul_le_mul_of_nonneg_left hι (by positivity)
      have b2 : H ^ 3 * L * (5 * L) ≤ 9 * (H ^ 4 * L ^ 2) := by
        have : H ^ 3 * L ^ 2 ≤ H ^ 4 * L ^ 2 := mul_le_mul_of_nonneg_right hH3 (sq_nonneg L)
        nlinarith
      have e : (3 * H ^ 2 * L) ^ 2 = 9 * (H ^ 4 * L ^ 2) := by ring
      linarith
    have a1 : 336 * H * (cb * Real.sqrt (H ^ 3 * L)) * (S * C * Real.sqrt ι') ≤
        1008 * cb * (H ^ 3 * S * C * L) := by
      have e : 336 * H * (cb * Real.sqrt (H ^ 3 * L)) * (S * C * Real.sqrt ι') =
          336 * H * cb * S * C * (Real.sqrt (H ^ 3 * L) * Real.sqrt ι') := by ring
      rw [e]
      calc _ ≤ 336 * H * cb * S * C * (3 * H ^ 2 * L) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = _ := by ring
    have a2 : 1008 * cb * (H ^ 3 * S * C * L) ≤ 1008 * cb / ca * P := by
      have : H ^ 3 * S * C * L ≤ H ^ 4 * S * C * L := by
        have hSCL : 0 ≤ S * C * L := by positivity
        have := mul_le_mul_of_nonneg_right hH3 hSCL
        linarith [show H ^ 3 * S * C * L = H ^ 3 * (S * C * L) by ring,
          show H ^ 4 * S * C * L = H ^ 4 * (S * C * L) by ring]
      have e : 1008 * cb / ca * P = 1008 * cb * (H ^ 4 * S * C * L) := by
        simp only [P]; field_simp
      rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
    exact a1.trans (a2.trans (mul_le_mul_of_nonneg_left hP (by positivity)))
  -- total
  rw [div_le_iff₀ hK]
  have hsum : 61 / ca + 840 / ca + 0.48 + 1008 * cb / ca ≤ 1 := by
    have h1 : 61 / ca ≤ 61 / (25 * 10 ^ 6) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hca0
    have h2 : 840 / ca ≤ 840 / (25 * 10 ^ 6) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hca0
    have h3 : 1008 * cb / ca = 1008 / (10 ^ 6 * cb) := by simp only [ca]; field_simp
    have h4 : 1008 / (10 ^ 6 * cb) ≤ 1008 / (10 ^ 6 * 5) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    rw [h3]; norm_num at h1 h2 h4 ⊢; linarith
  have hεK : 0 ≤ ε * K := by positivity
  have expand : 21 * H * (2 * H * S * C + 8 * C * H ^ 2 * ι' +
      16 * (cb * Real.sqrt (H ^ 3 * L)) * (Real.sqrt (2 * K * C * S) + S * C * Real.sqrt ι')) =
      42 * H ^ 2 * S * C + 168 * C * H ^ 3 * ι' +
      336 * H * (cb * Real.sqrt (H ^ 3 * L)) * Real.sqrt (2 * K * C * S) +
      336 * H * (cb * Real.sqrt (H ^ 3 * L)) * (S * C * Real.sqrt ι') := by ring
  rw [expand]
  have : (61 / ca + 840 / ca + 0.48 + 1008 * cb / ca) * (ε * K) ≤ 1 * (ε * K) :=
    mul_le_mul_of_nonneg_right hsum hεK
  nlinarith [t1, t2, t3, t4, this]

end StatisticalRL.LCBQFinite
