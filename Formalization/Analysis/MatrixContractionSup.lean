import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# Ordered matrix products and sup-norm contraction bounds

Generic facts (no RL content) used for linearised stochastic-approximation recursions
`x_{t+1} = B_t x_t + u_t` on `n → ℝ` with the sup norm.

* `matProd B m t = B_{t−1} ⋯ B_m` for `m ≤ t` (left multiplication, the latest factor first), and
  `1` for `t ≤ m` (`matProd_of_le`, `matProd_succ`).
* `norm_matProd_mulVec_le`: if every `B_i` contracts by `c_i ≥ 0`, then
  `‖matProd B m t v‖ ≤ (∏_{i ∈ [m,t)} c_i) ‖v‖`.
* `linRec_eq`, `sum_linRec_eq`: the variation-of-constants formula and its summed form
  `∑_{t<T} x_{t+1} = (∑_{t<T} matProd B 0 (t+1)) x_0 + ∑_{k<T} (∑_{t ∈ [k,T)} matProd B (k+1) (t+1)) u_k`.
* `sum_abs_le_of_norm_mulVec_le`: an operator bound `‖X v‖ ≤ c ‖v‖` bounds every absolute row
  sum of `X` by `c`; `abs_mul_diagonal_mul_transpose_sub_le`: an entrywise bound for
  `W D Wᵀ − V D Vᵀ` with `D` diagonal.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered product `B_{t−1} ⋯ B_{m+1} B_m` for `m ≤ t`; the identity for `t ≤ m`. -/
def matProd (B : ℕ → Matrix n n ℝ) (m : ℕ) : ℕ → Matrix n n ℝ
  | 0 => 1
  | t + 1 => if m ≤ t then B t * matProd B m t else 1

theorem matProd_of_le (B : ℕ → Matrix n n ℝ) {m t : ℕ} (h : t ≤ m) : matProd B m t = 1 := by
  cases t with
  | zero => rfl
  | succ t => rw [matProd, if_neg (by omega)]

theorem matProd_self (B : ℕ → Matrix n n ℝ) (m : ℕ) : matProd B m m = 1 :=
  matProd_of_le B le_rfl

theorem matProd_succ (B : ℕ → Matrix n n ℝ) {m t : ℕ} (h : m ≤ t) :
    matProd B m (t + 1) = B t * matProd B m t := by
  rw [matProd, if_pos h]

/-- Product contraction: `‖matProd B m t v‖ ≤ (∏_{i ∈ [m,t)} c_i) ‖v‖`. -/
theorem norm_matProd_mulVec_le (B : ℕ → Matrix n n ℝ) (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hB : ∀ i (v : n → ℝ), ‖B i *ᵥ v‖ ≤ c i * ‖v‖) (m t : ℕ) (v : n → ℝ) :
    ‖matProd B m t *ᵥ v‖ ≤ (∏ i ∈ Ico m t, c i) * ‖v‖ := by
  induction t with
  | zero => simp [matProd]
  | succ t ih =>
    by_cases h : m ≤ t
    · rw [matProd_succ B h, ← mulVec_mulVec, prod_Ico_succ_top h]
      calc ‖B t *ᵥ (matProd B m t *ᵥ v)‖ ≤ c t * ‖matProd B m t *ᵥ v‖ := hB t _
        _ ≤ c t * ((∏ i ∈ Ico m t, c i) * ‖v‖) := mul_le_mul_of_nonneg_left ih (hc t)
        _ = _ := by ring
    · rw [matProd_of_le B (by omega), Ico_eq_empty (by omega)]
      simp

/-- Variation of constants for `x_{t+1} = B_t x_t + u_t` (`t < T`):
`x_t = matProd B 0 t x_0 + ∑_{k<t} matProd B (k+1) t u_k` for `t ≤ T`. -/
theorem linRec_eq (B : ℕ → Matrix n n ℝ) (x u : ℕ → n → ℝ) {T : ℕ}
    (hx : ∀ t < T, x (t + 1) = B t *ᵥ x t + u t) {t : ℕ} (ht : t ≤ T) :
    x t = matProd B 0 t *ᵥ x 0 + ∑ k ∈ range t, matProd B (k + 1) t *ᵥ u k := by
  induction t with
  | zero => simp [matProd]
  | succ t ih =>
    rw [hx t (by omega), ih (by omega), sum_range_succ, matProd_self, one_mulVec,
      matProd_succ B (Nat.zero_le t), ← mulVec_mulVec, mulVec_add, mulVec_sum, add_assoc]
    congr 2
    refine sum_congr rfl fun k hk ↦ ?_
    rw [matProd_succ B (by simp at hk; omega), ← mulVec_mulVec]

/-- The summed variation-of-constants formula. -/
theorem sum_linRec_eq (B : ℕ → Matrix n n ℝ) (x u : ℕ → n → ℝ) {T : ℕ}
    (hx : ∀ t < T, x (t + 1) = B t *ᵥ x t + u t) :
    ∑ t ∈ range T, x (t + 1) = (∑ t ∈ range T, matProd B 0 (t + 1)) *ᵥ x 0 +
      ∑ k ∈ range T, (∑ t ∈ Ico k T, matProd B (k + 1) (t + 1)) *ᵥ u k := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hx' : ∀ t < T, x (t + 1) = B t *ᵥ x t + u t := fun t ht ↦ hx t (by omega)
    have hlast := linRec_eq B x u hx (le_refl (T + 1))
    have hsplit : ∀ k ∈ range (T + 1),
        (∑ t ∈ Ico k (T + 1), matProd B (k + 1) (t + 1)) *ᵥ u k =
          (∑ t ∈ Ico k T, matProd B (k + 1) (t + 1)) *ᵥ u k +
            matProd B (k + 1) (T + 1) *ᵥ u k := by
      intro k hk
      rw [sum_Ico_succ_top (by simp at hk; omega), add_mulVec]
    rw [sum_range_succ (fun t ↦ x (t + 1)), ih hx', hlast, sum_congr rfl hsplit, sum_add_distrib,
      sum_range_succ (fun k ↦ (∑ t ∈ Ico k T, matProd B (k + 1) (t + 1)) *ᵥ u k), Ico_self,
      sum_empty, zero_mulVec, add_zero, sum_range_succ (fun t ↦ matProd B 0 (t + 1)), add_mulVec]
    abel

omit [DecidableEq n] in
/-- An operator bound `‖X v‖_∞ ≤ c ‖v‖_∞` (`c ≥ 0`) bounds each absolute row sum by `c`. -/
theorem sum_abs_le_of_norm_mulVec_le (X : Matrix n n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∀ v : n → ℝ, ‖X *ᵥ v‖ ≤ c * ‖v‖) (s : n) : ∑ u, |X s u| ≤ c := by
  set v : n → ℝ := fun u ↦ if 0 ≤ X s u then 1 else -1 with hv
  have hvn : ‖v‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun u ↦ ?_
    simp only [hv]
    split_ifs <;> simp
  have h1 : (X *ᵥ v) s = ∑ u, |X s u| := by
    simp only [mulVec, dotProduct, hv]
    refine sum_congr rfl fun u _ ↦ ?_
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (not_le.1 h)]; ring
  calc ∑ u, |X s u| = (X *ᵥ v) s := h1.symm
    _ ≤ |(X *ᵥ v) s| := le_abs_self _
    _ ≤ ‖X *ᵥ v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ s
    _ ≤ c * ‖v‖ := hX v
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hvn hc
    _ = c := mul_one c

omit [DecidableEq n] in
theorem abs_apply_le_of_norm_mulVec_le (X : Matrix n n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∀ v : n → ℝ, ‖X *ᵥ v‖ ≤ c * ‖v‖) (s u : n) : |X s u| ≤ c :=
  (single_le_sum (f := fun u ↦ |X s u|) (fun _ _ ↦ abs_nonneg _) (mem_univ u)).trans
    (sum_abs_le_of_norm_mulVec_le X hc hX s)

theorem mul_diagonal_mul_transpose_apply (X Y : Matrix n n ℝ) (d : n → ℝ) (s s' : n) :
    (X * diagonal d * Yᵀ) s s' = ∑ u, X s u * d u * Y s' u := by
  simp only [mul_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, if_true]

omit [DecidableEq n] in
theorem abs_sum_mul_mul_le (x g y : n → ℝ) {G K : ℝ} (hG : 0 ≤ G) (hg : ∀ u, |g u| ≤ G)
    (hy : ∀ u, |y u| ≤ K) : |∑ u, x u * g u * y u| ≤ (∑ u, |x u|) * (G * K) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun u _ ↦ ?_
  rw [abs_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hg u) (hy u) (abs_nonneg _) hG) (abs_nonneg _)

/-- Entrywise bound for `W D Wᵀ − V D Vᵀ`, `D = diag(d)`: if `|d| ≤ G`, `|W s' ·| ≤ K`,
`|V s ·| ≤ L` and both absolute row sums of `W − V` at `s`, `s'` are at most `e`, then
`|(W D Wᵀ − V D Vᵀ)(s,s')| ≤ G (K + L) e`. -/
theorem abs_mul_diagonal_mul_transpose_sub_le (W V : Matrix n n ℝ) (d : n → ℝ) (s s' : n)
    {G K L e : ℝ} (hG : 0 ≤ G) (hd : ∀ u, |d u| ≤ G) (hW : ∀ u, |W s' u| ≤ K)
    (hV : ∀ u, |V s u| ≤ L) (he : ∑ u, |(W - V) s u| ≤ e) (he' : ∑ u, |(W - V) s' u| ≤ e) :
    |(W * diagonal d * Wᵀ) s s' - (V * diagonal d * Vᵀ) s s'| ≤ G * (K + L) * e := by
  rw [mul_diagonal_mul_transpose_apply, mul_diagonal_mul_transpose_apply]
  have hsplit : ∑ u, W s u * d u * W s' u - ∑ u, V s u * d u * V s' u =
      ∑ u, (W - V) s u * d u * W s' u + ∑ u, (W - V) s' u * d u * V s u := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    simp only [sub_apply]
    ring
  have hK : 0 ≤ K := (abs_nonneg _).trans (hW s')
  rw [hsplit]
  have h1 := abs_sum_mul_mul_le (fun u ↦ (W - V) s u) d (fun u ↦ W s' u) hG hd hW
  have h2 := abs_sum_mul_mul_le (fun u ↦ (W - V) s' u) d (fun u ↦ V s u) hG hd hV
  have he0 : 0 ≤ e := (sum_nonneg fun _ _ ↦ abs_nonneg _).trans he
  have hL : 0 ≤ L := (abs_nonneg _).trans (hV s)
  calc _ ≤ |∑ u, (W - V) s u * d u * W s' u| + |∑ u, (W - V) s' u * d u * V s u| :=
        abs_add_le _ _
    _ ≤ (∑ u, |(W - V) s u|) * (G * K) + (∑ u, |(W - V) s' u|) * (G * L) := add_le_add h1 h2
    _ ≤ e * (G * K) + e * (G * L) :=
        add_le_add (mul_le_mul_of_nonneg_right he (mul_nonneg hG hK))
          (mul_le_mul_of_nonneg_right he' (mul_nonneg hG hL))
    _ = G * (K + L) * e := by ring

end StatisticalRL.Analysis
