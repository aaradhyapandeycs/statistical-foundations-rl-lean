import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Telescoping bound for `∑ j^{-3/2}` and the reservoir budget arithmetic

Infrastructure for the all-convex route to Theorem 7.11 (`thm:Berry-Esseen-linear`,
`chapters/inference.tex:132–141`): the arithmetic of the reservoir Lindeberg swap, pass 1
(milestone M5a, lemmas L23–L26 of the M5a design). Planner/P0 construction; not from a cited
paper, and not a source result.

* `inv_mul_sqrt_le_four_mul_sub`: `j^{-3/2} ≤ 4 (j^{-1/2} − (j+1)^{-1/2})` for `j ≥ 1`;
* `sum_Ico_inv_mul_sqrt_le`: `∑_{J ≤ j < N} j^{-3/2} ≤ 4 / √J`;
* `sum_range_le_reservoir_budget`: if step `k < n` costs `≤ Aa · j^{-3/2}` when the reservoir size
  `j = n − 1 − k` (a natural number) is at least `J`, and `≤ Ac` otherwise, the total cost is
  `≤ J · Ac + 4 Aa / √J`;
* `quarter_arith`, `sum_range_le_quarter`: the choice `J = r₀ + ⌈√n⌉`, `ε = n^{-1/4}` gives the
  pass-1 rate `n^{-1/4}` with an explicit constant.

The reservoir size is kept as the natural number `n - 1 - k` and cast to `ℝ` once.
-/

open Finset Real

namespace StatisticalRL.Analysis

/-- L23. `j^{-3/2} ≤ 4 (j^{-1/2} − (j+1)^{-1/2})` for `j ≥ 1`. -/
theorem inv_mul_sqrt_le_four_mul_sub {j : ℕ} (hj : 1 ≤ j) :
    ((j : ℝ) * √(j : ℝ))⁻¹ ≤ 4 * ((√(j : ℝ))⁻¹ - (√((j + 1 : ℕ) : ℝ))⁻¹) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set a := √(j : ℝ) with ha_def
  set b := √((j + 1 : ℕ) : ℝ) with hb_def
  have ha2 : a ^ 2 = j := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = j + 1 := by
    rw [hb_def, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have ha1 : 1 ≤ a := by
    rw [ha_def]
    exact Real.one_le_sqrt.2 hj1
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hab : a ≤ b := by nlinarith
  have hb1 : 1 ≤ b := le_trans ha1 hab
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hjeq : (j : ℝ) = a ^ 2 := ha2.symm
  have key : 4 * (a⁻¹ - b⁻¹) = 4 / (a * b * (a + b)) := by
    field_simp
    nlinarith
  rw [key, hjeq, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hapos hbpos, sq_nonneg (a - b)]

/-- L24. Telescoping: `∑_{J ≤ j < N} j^{-3/2} ≤ 4 / √J` for `J ≥ 1`. -/
theorem sum_Ico_inv_mul_sqrt_le {J : ℕ} (hJ : 1 ≤ J) (N : ℕ) :
    ∑ j ∈ Finset.Ico J N, ((j : ℝ) * √(j : ℝ))⁻¹ ≤ 4 / √(J : ℝ) := by
  have htel : ∀ m : ℕ, ∑ j ∈ Finset.Ico J (J + m), ((j : ℝ) * √(j : ℝ))⁻¹ ≤
      4 * ((√(J : ℝ))⁻¹ - (√((J + m : ℕ) : ℝ))⁻¹) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right J m)]
      have h := inv_mul_sqrt_le_four_mul_sub (j := J + m) (by omega)
      calc _ ≤ 4 * ((√(J : ℝ))⁻¹ - (√((J + m : ℕ) : ℝ))⁻¹) +
            4 * ((√((J + m : ℕ) : ℝ))⁻¹ - (√((J + m + 1 : ℕ) : ℝ))⁻¹) := add_le_add ih h
        _ = _ := by ring
  rcases le_or_gt N J with hNJ | hNJ
  · rw [Finset.Ico_eq_empty_of_le hNJ, Finset.sum_empty]
    positivity
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNJ.le
    refine (htel m).trans ?_
    have : 0 ≤ (√((J + m : ℕ) : ℝ))⁻¹ := by positivity
    rw [div_eq_mul_inv]
    linarith

/-- L25. Pass-1 budget: if step `k < n` costs at most `Aa · j^{-3/2}` when the reservoir size
`j = n − 1 − k` satisfies `J ≤ j`, and at most `Ac` otherwise, then the total is
`≤ J · Ac + 4 Aa / √J`. -/
theorem sum_range_le_reservoir_budget {n J : ℕ} (hJ : 1 ≤ J) {a : ℕ → ℝ} {Aa Ac : ℝ}
    (hAc : 0 ≤ Ac)
    (ha : ∀ k < n, J ≤ n - 1 - k →
      a k ≤ Aa * (((n - 1 - k : ℕ) : ℝ) * √((n - 1 - k : ℕ) : ℝ))⁻¹)
    (hc : ∀ k < n, n - 1 - k < J → a k ≤ Ac) (hAa : 0 ≤ Aa) :
    ∑ k ∈ Finset.range n, a k ≤ J * Ac + 4 * Aa / √(J : ℝ) := by
  set g : ℕ → ℝ := fun j ↦ ((j : ℝ) * √(j : ℝ))⁻¹ with hg
  set F₁ : ℕ → ℝ := fun j ↦ if J ≤ j then Aa * g j else 0 with hF₁
  set F₂ : ℕ → ℝ := fun j ↦ if J ≤ j then 0 else Ac with hF₂
  have hsplit : ∀ k ∈ Finset.range n, a k ≤ F₁ (n - 1 - k) + F₂ (n - 1 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases h : J ≤ n - 1 - k
    · simp only [hF₁, hF₂, if_pos h, add_zero]
      exact ha k hk h
    · simp only [hF₁, hF₂, if_neg h, zero_add]
      exact hc k hk (by omega)
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib,
    Finset.sum_range_reflect F₁ n, Finset.sum_range_reflect F₂ n]
  have h1 : ∑ j ∈ Finset.range n, F₁ j ≤ 4 * Aa / √(J : ℝ) := by
    have hfil : ∑ j ∈ Finset.range n, F₁ j = Aa * ∑ j ∈ Finset.Ico J n, g j := by
      rw [hF₁, ← Finset.sum_filter, Finset.mul_sum]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfil, mul_comm 4 Aa, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_sqrt_le hJ n) hAa
  have h2 : ∑ j ∈ Finset.range n, F₂ j ≤ J * Ac := by
    have hfil : ∑ j ∈ Finset.range n, F₂ j =
        ∑ j ∈ (Finset.range n).filter (fun j ↦ ¬ J ≤ j), Ac := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases h : J ≤ j <;> simp [hF₂, h]
    rw [hfil, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hAc
    have hsub : (Finset.range n).filter (fun j ↦ ¬ J ≤ j) ⊆ Finset.range J := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  linarith

/-- L26. The pass-1 arithmetic for `J = r₀ + ⌈√n⌉` and `ε = n^{-1/4}` (so `ε⁻¹ = √√n`):
`J · Ac + 4 Aa / √J ≤ (A₃ B³ / 6)(c₃ (2 + r₀) + 4 C_H (c √c)⁻¹) / √√n`, with
`Ac = c₃ ε^{-3} / 6 · A₃ (B/√n)³` and `Aa = C_H (c√c)⁻¹ / 6 · A₃ B³`. -/
theorem quarter_arith {n : ℕ} (hn : 0 < n) {c₃ C_H A₃ B c : ℝ} (r₀ : ℕ)
    (hc₃ : 0 ≤ c₃) (hCH : 0 ≤ C_H) (hA₃ : 0 ≤ A₃) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    ((r₀ + ⌈√(n : ℝ)⌉₊ : ℕ) : ℝ) * (c₃ * (√√(n : ℝ)) ^ 3 / 6 * A₃ * (B / √(n : ℝ)) ^ 3)
      + 4 * (C_H * (c * √c)⁻¹ / 6 * A₃ * B ^ 3) / √((r₀ + ⌈√(n : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ A₃ * B ^ 3 / 6 * (c₃ * (2 + r₀) + 4 * C_H * (c * √c)⁻¹) / √√(n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set q := √√(n : ℝ) with hq_def
  have hsn : √(n : ℝ) = q ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have hsn1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 hn1
  have hq1 : 1 ≤ q := Real.one_le_sqrt.2 hsn1
  have hqpos : 0 < q := by linarith
  set J : ℕ := r₀ + ⌈√(n : ℝ)⌉₊ with hJ_def
  have hceil_lt : (⌈√(n : ℝ)⌉₊ : ℝ) < √(n : ℝ) + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hceil_ge : √(n : ℝ) ≤ (⌈√(n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hJle : (J : ℝ) ≤ r₀ + q ^ 2 + 1 := by
    rw [hJ_def]
    push_cast
    rw [← hsn]
    linarith
  have hJge : q ^ 2 ≤ (J : ℝ) := by
    rw [hJ_def]
    push_cast
    rw [← hsn]
    have : (0 : ℝ) ≤ r₀ := by positivity
    linarith
  have hsJ : q ≤ √(J : ℝ) := by
    rw [show q = √(q ^ 2) from (Real.sqrt_sq hqpos.le).symm]
    exact Real.sqrt_le_sqrt hJge
  have hsJpos : 0 < √(J : ℝ) := lt_of_lt_of_le hqpos hsJ
  set K := A₃ * B ^ 3 / 6 with hK
  have hK0 : 0 ≤ K := by positivity
  set D := C_H * (c * √c)⁻¹ with hD
  have hD0 : 0 ≤ D := by positivity
  have hlhs : (J : ℝ) * (c₃ * q ^ 3 / 6 * A₃ * (B / √(n : ℝ)) ^ 3)
      + 4 * (C_H * (c * √c)⁻¹ / 6 * A₃ * B ^ 3) / √(J : ℝ)
      = K * c₃ * ((J : ℝ) / q ^ 3) + 4 * K * D * (1 / √(J : ℝ)) := by
    rw [hsn, hK, hD]
    field_simp
  have hrhs : K * (c₃ * (2 + r₀) + 4 * C_H * (c * √c)⁻¹) / q
      = K * c₃ * ((2 + r₀) / q) + 4 * K * D * (1 / q) := by
    rw [hD]
    field_simp
  rw [hlhs, hrhs]
  have hp1 : (J : ℝ) / q ^ 3 ≤ (2 + r₀) / q := by
    rw [div_le_div_iff₀ (by positivity) hqpos]
    have hq3 : q ≤ q ^ 3 := by nlinarith
    have hr0 : (0 : ℝ) ≤ r₀ := by positivity
    nlinarith
  have hp2 : 1 / √(J : ℝ) ≤ 1 / q := one_div_le_one_div_of_le hqpos hsJ
  have := mul_le_mul_of_nonneg_left hp1 (mul_nonneg hK0 hc₃)
  have := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ 4 * K * D)
  linarith

/-- L25 + L26: the pass-1 total for per-step costs bounded as in the reservoir Lindeberg swap. -/
theorem sum_range_le_quarter {n : ℕ} (hn : 0 < n) {c₃ C_H A₃ B c : ℝ} (r₀ : ℕ)
    (hc₃ : 0 ≤ c₃) (hCH : 0 ≤ C_H) (hA₃ : 0 ≤ A₃) (hB : 0 ≤ B) (hc : 0 ≤ c) {a : ℕ → ℝ}
    (ha : ∀ k < n, r₀ + ⌈√(n : ℝ)⌉₊ ≤ n - 1 - k →
      a k ≤ C_H * (c * √c)⁻¹ / 6 * A₃ * B ^ 3 *
        (((n - 1 - k : ℕ) : ℝ) * √((n - 1 - k : ℕ) : ℝ))⁻¹)
    (hc' : ∀ k < n, n - 1 - k < r₀ + ⌈√(n : ℝ)⌉₊ →
      a k ≤ c₃ * (√√(n : ℝ)) ^ 3 / 6 * A₃ * (B / √(n : ℝ)) ^ 3) :
    ∑ k ∈ Finset.range n, a k ≤
      A₃ * B ^ 3 / 6 * (c₃ * (2 + r₀) + 4 * C_H * (c * √c)⁻¹) / √√(n : ℝ) := by
  have hJ : 1 ≤ r₀ + ⌈√(n : ℝ)⌉₊ := by
    have : 0 < ⌈√(n : ℝ)⌉₊ := Nat.ceil_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))
    omega
  refine (sum_range_le_reservoir_budget hJ (by positivity) ha hc' (by positivity)).trans ?_
  exact quarter_arith hn r₀ hc₃ hCH hA₃ hB hc

end StatisticalRL.Analysis
