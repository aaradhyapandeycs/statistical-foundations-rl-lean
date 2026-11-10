import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Theorem 7.6: arithmetic at the printed threshold

* `two_pow_card_le_prod`, `two_mul_card_le_prod`: with `M = #{i : A_i ≥ 2}` and all `A_i ≥ 1`,
  `2^M ≤ ∏ A_i` and `2M ≤ ∏ A_i`.
* `log_absorb`: `log(16 M H S |𝒜| / δ) ≤ 3 log(S H N |𝒜| / δ)` when `H ≥ 2`, `|𝒜| ≥ 2`, `S, N ≥ 1`,
  `0 < δ < 1` and `2M ≤ |𝒜|` (the factor 3 is a supremum, not attained).
* `final_arith`: at the printed threshold `400 H³ Λ / ε² ≤ N` with `ε² ≤ H`, `0 ≤ L ≤ 3Λ`,
  the choice `λ = ε/(8H²)` gives `H √(2L/N) ≤ 1/2` and
  `2 (λH² + 2HL/(λN) + (4/3)H²L/N) ≤ ε`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

theorem two_mul_le_two_pow (M : ℕ) : 2 * M ≤ 2 ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp
    · have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
      rw [pow_succ]; omega

theorem two_pow_card_le_prod {m : ℕ} (A : Fin m → ℕ) (hA : ∀ i, 0 < A i) :
    2 ^ (Finset.univ.filter (fun i => 2 ≤ A i)).card ≤ ∏ i, A i := by
  classical
  have h1 : ∏ i, (if 2 ≤ A i then 2 else 1) = 2 ^ (Finset.univ.filter (fun i => 2 ≤ A i)).card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rw [← h1]
  refine Finset.prod_le_prod' fun i _ => ?_
  split_ifs with h
  · exact h
  · exact hA i

theorem two_mul_card_le_prod {m : ℕ} (A : Fin m → ℕ) (hA : ∀ i, 0 < A i) :
    2 * (Finset.univ.filter (fun i => 2 ≤ A i)).card ≤ ∏ i, A i :=
  (two_mul_le_two_pow _).trans (two_pow_card_le_prod A hA)

theorem log_absorb (M H S N P δ : ℝ) (hH : 2 ≤ H) (hP : 2 ≤ P) (hS : 1 ≤ S) (hN : 1 ≤ N)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hMP : 2 * M ≤ P) (hM1 : 1 ≤ M) :
    Real.log (4 * (4 * M * H * S * P) / δ) ≤ 3 * Real.log (S * H * N * P / δ) := by
  have hpos : 0 < 4 * (4 * M * H * S * P) / δ := by positivity
  rw [← Real.log_rpow (by positivity)]
  apply Real.log_le_log hpos
  have hx : S * H * P / δ ≤ S * H * N * P / δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    have : S * H * P * 1 ≤ S * H * P * N := mul_le_mul_of_nonneg_left hN (by positivity)
    nlinarith
  have hrp : (S * H * N * P / δ) ^ (3 : ℝ) = (S * H * N * P / δ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [hrp]
  have hy0 : 0 ≤ S * H * P / δ := by positivity
  have h3 : (S * H * P / δ) ^ 3 ≤ (S * H * N * P / δ) ^ 3 := pow_le_pow_left₀ hy0 hx 3
  refine le_trans ?_ h3
  -- `16 M H S P / δ ≤ (S H P / δ)^3`
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ, mul_pos hδ hδ]
  have hnum : 4 * (4 * M * H * S * P) ≤ (S * H * P) ^ 3 := by
    have hS2 : 1 ≤ S ^ 2 := by nlinarith
    have hH2 : 4 ≤ H ^ 2 := by nlinarith
    have hSH : 4 ≤ S ^ 2 * H ^ 2 := by nlinarith
    have h8 : 8 ≤ S ^ 2 * H ^ 2 * P := by nlinarith
    have h16 : 4 * (4 * M * H * S * P) ≤ 8 * H * S * P ^ 2 := by nlinarith [mul_pos (by linarith : (0:ℝ) < H) (by linarith : (0:ℝ) < S)]
    have : 8 * H * S * P ^ 2 ≤ (S * H * P) ^ 3 := by
      have hHSP : 0 ≤ H * S * P ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h8 hHSP]
    linarith
  rw [div_pow]
  rw [div_le_div_iff₀ hδ (by positivity)]
  have : 4 * (4 * M * H * S * P) * δ ^ 3 ≤ 4 * (4 * M * H * S * P) * δ :=
    mul_le_mul_of_nonneg_left hδ3 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hnum hδ.le]

theorem final_arith (H ε Λ L Nr : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hεH : ε ^ 2 ≤ H)
    (hN : 0 < Nr) (hL : 0 ≤ L) (hLΛ : L ≤ 3 * Λ)
    (hthr : 400 * H ^ 3 / ε ^ 2 * Λ ≤ Nr) :
    H * Real.sqrt (2 * L / Nr) ≤ 1 / 2 ∧
      2 * (ε / (8 * H ^ 2) * H ^ 2 + 2 * H * L / (ε / (8 * H ^ 2) * Nr) +
        4 / 3 * H ^ 2 * L / Nr) ≤ ε := by
  have hH0 : 0 < H := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  -- `T := H³L ≤ 3 N ε² / 400`
  have hΛ : 400 * H ^ 3 * Λ ≤ Nr * ε ^ 2 := by
    have := hthr
    rw [div_mul_eq_mul_div, div_le_iff₀ hε2] at this
    linarith
  have hT : H ^ 3 * L ≤ 3 * Nr * ε ^ 2 / 400 := by
    have : H ^ 3 * L ≤ H ^ 3 * (3 * Λ) := mul_le_mul_of_nonneg_left hLΛ (by positivity)
    linarith
  have hεle : ε ≤ H := by
    by_cases h1 : ε ≤ 1
    · linarith
    · push_neg at h1; nlinarith
  constructor
  · set y := H * Real.sqrt (2 * L / Nr)
    have hy0 : 0 ≤ y := by positivity
    have hy2 : y ^ 2 = H ^ 2 * (2 * L / Nr) := by
      simp only [y]; rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hy2' : y ^ 2 ≤ 1 / 4 := by
      rw [hy2]
      have : H ^ 2 * (2 * L / Nr) = 2 * (H ^ 3 * L) / (H * Nr) := by field_simp
      rw [this, div_le_iff₀ (by positivity)]
      have h1 : 2 * (H ^ 3 * L) ≤ 6 * Nr * ε ^ 2 / 400 := by linarith
      have h2 : 6 * Nr * ε ^ 2 / 400 ≤ 6 * Nr * H / 400 := by
        have := mul_le_mul_of_nonneg_left hεH (by positivity : (0:ℝ) ≤ 6 * Nr)
        linarith
      nlinarith
    nlinarith
  · have hA : ε / (8 * H ^ 2) * H ^ 2 = ε / 8 := by field_simp
    have hB : 2 * H * L / (ε / (8 * H ^ 2) * Nr) ≤ 12 / 100 * ε := by
      have : 2 * H * L / (ε / (8 * H ^ 2) * Nr) = 16 * (H ^ 3 * L) / (ε * Nr) := by
        field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    have hC : 4 / 3 * H ^ 2 * L / Nr ≤ 1 / 100 * ε := by
      have : 4 / 3 * H ^ 2 * L / Nr = 4 * (H ^ 3 * L) / (3 * H * Nr) := by field_simp
      rw [this, div_le_iff₀ (by positivity)]
      have h1 : 4 * (H ^ 3 * L) ≤ 12 * Nr * ε ^ 2 / 400 := by linarith
      have h2 : ε ^ 2 ≤ ε * H := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hN.le]
    rw [hA]
    linarith

end StatisticalRL.Ch7Rest.Marl76
