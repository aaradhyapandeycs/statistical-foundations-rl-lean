import Formalization.Online.QLearning.RateWeights
import Formalization.Online.QLearning.ReciprocalSqrt

/-!
# Counting identities for visit sequences (Theorem 6.17 analysis)

For a predicate `X` on episode indices (the visit indicator of one `(h,s,a)`), `cnt X k` is the
number of visits before episode `k`. This file proves the reindexing identities used in Steps 1(v)
and 4(c) of the plan: sums over visiting episodes become sums over visit numbers, the Q-learning
unrolling, the regrouping of a double sum, and the tail bound `Σ_{n ≥ i} η_i^n ≤ 1 + 1/H`.
-/

namespace StatisticalRL.LCBQFinite

open Finset OnlineRL

section

variable (X : ℕ → Prop) [DecidablePred X]

/-- Number of visits strictly before episode `k`. -/
def cnt (k : ℕ) : ℕ := ((range k).filter X).card

theorem cnt_zero : cnt X 0 = 0 := by simp [cnt]

theorem cnt_succ (k : ℕ) : cnt X (k + 1) = cnt X k + if X k then 1 else 0 := by
  unfold cnt
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_succ_of (k : ℕ) (h : X k) : cnt X (k + 1) = cnt X k + 1 := by
  rw [cnt_succ, if_pos h]

theorem cnt_succ_of_not (k : ℕ) (h : ¬ X k) : cnt X (k + 1) = cnt X k := by
  rw [cnt_succ, if_neg h, add_zero]

theorem cnt_mono {k k' : ℕ} (hk : k ≤ k') : cnt X k ≤ cnt X k' := by
  unfold cnt
  exact card_le_card (filter_subset_filter _ (range_subset_range.2 hk))

theorem cnt_le (k : ℕ) : cnt X k ≤ k := by
  unfold cnt
  exact (card_filter_le _ _).trans (by simp)

theorem cnt_lt_of {j k : ℕ} (hj : X j) (hjk : j < k) : cnt X j + 1 ≤ cnt X k := by
  rw [← cnt_succ_of X j hj]
  exact cnt_mono X hjk

theorem cnt_succ_le (k : ℕ) : cnt X (k + 1) ≤ cnt X k + 1 := by
  rw [cnt_succ]; split_ifs <;> omega

/-- **(C2)** Sums over visiting episodes in `[a, k)` are sums over visit numbers. -/
theorem sum_Ico_visits (f : ℕ → ℝ) {a k : ℕ} (hak : a ≤ k) :
    ∑ j ∈ Ico a k, (if X j then f (cnt X j) else 0) = ∑ i ∈ Ico (cnt X a) (cnt X k), f i := by
  induction k, hak using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    rw [sum_Ico_succ_top hak, ih]
    by_cases hx : X k
    · rw [if_pos hx, cnt_succ_of X k hx, sum_Ico_succ_top (cnt_mono X hak)]
    · rw [if_neg hx, cnt_succ_of_not X k hx, add_zero]

theorem sum_range_visits (f : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ range k, (if X j then f (cnt X j) else 0) = ∑ i ∈ range (cnt X k), f i := by
  have := sum_Ico_visits X f (Nat.zero_le k)
  rw [cnt_zero] at this
  rw [range_eq_Ico]
  exact this

/-- **(U)** The Q-learning unrolling along a visit sequence: with `Q_0 = 0` and the update
`Q ← (1-η_n) Q + η_n y` at visits, `Q_k = Σ_{j<k, X j} η^{cnt k}_{cnt j + 1} y_j`. -/
theorem unroll {H : ℕ} (Q y : ℕ → ℝ) (hQ0 : Q 0 = 0)
    (hQ : ∀ k, Q (k + 1) = if X k then (1 - onlineQRate H (cnt X k + 1)) * Q k +
      onlineQRate H (cnt X k + 1) * y k else Q k) :
    ∀ k, Q k = ∑ j ∈ range k,
      (if X j then onlineQRateWeight H (cnt X k) (cnt X j + 1) * y j else 0) := by
  intro k
  induction k with
  | zero => simp [hQ0]
  | succ k ih =>
    rw [hQ k, sum_range_succ]
    by_cases hx : X k
    · rw [if_pos hx, if_pos hx, cnt_succ_of X k hx, ih,
        onlineQRateWeight_self (by omega : 1 ≤ cnt X k + 1), mul_sum]
      congr 1
      refine sum_congr rfl fun j hj ↦ ?_
      split_ifs with hxj
      · rw [onlineQRateWeight_succ (by omega) (cnt_lt_of X hxj (mem_range.1 hj))]
        ring
      · simp
    · rw [if_neg hx, if_neg hx, cnt_succ_of_not X k hx, ih, add_zero]

/-- **(C3)** Regrouping a double sum over pairs of visits `j < k`. -/
theorem regroup (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ range K, (if X k then ∑ j ∈ range k,
        (if X j then c (cnt X k) (cnt X j) * g j else 0) else 0) =
      ∑ j ∈ range K, (if X j then g j * ∑ n ∈ Ico (cnt X j + 1) (cnt X K), c n (cnt X j)
        else 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j ↦ if X j then g j *
      ∑ n ∈ Ico (cnt X j + 1) (cnt X (K + 1)), c n (cnt X j) else 0)]
    have hlast : (if X K then g K * ∑ n ∈ Ico (cnt X K + 1) (cnt X (K + 1)), c n (cnt X K)
        else 0) = 0 := by
      split_ifs
      · rw [Ico_eq_empty (by have := cnt_succ_le X K; omega), sum_empty, mul_zero]
      · rfl
    rw [hlast, add_zero]
    by_cases hx : X K
    · rw [if_pos hx, ← sum_add_distrib]
      refine sum_congr rfl fun j hj ↦ ?_
      split_ifs with hxj
      · have hle := cnt_lt_of X hxj (mem_range.1 hj)
        rw [cnt_succ_of X K hx, sum_Ico_succ_top (by omega)]
        ring
      · simp
    · rw [if_neg hx, add_zero]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [cnt_succ_of_not X K hx]

end

/-- **Tail bound** `Σ_{n ∈ [i, N)} η_i^n ≤ 1 + 1/H` for `i ≥ 1` (`eq:properties-learning-rates`). -/
theorem tail_le {H : ℕ} (hH : 0 < H) {i : ℕ} (hi : 1 ≤ i) (N : ℕ) :
    ∑ n ∈ Ico i N, onlineQRateWeight H n i ≤ 1 + 1 / (H : ℝ) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  rcases le_or_gt i N with hiN | hiN
  · rw [sum_Ico_eq_sum_range, onlineQRateWeight_tail_partial hH hi]
    have h1 : 0 ≤ ((H : ℝ) + i + ((N - i : ℕ) : ℝ)) / H * onlineQRateWeight H (i + (N - i)) i :=
      mul_nonneg (by positivity) (onlineQRateWeight_nonneg hH _ _)
    linarith
  · rw [Ico_eq_empty (by omega), sum_empty]
    positivity

/-- `Σ_{i<n} F(i+1) = Σ_{i ∈ [1,n]} F(i)`. -/
theorem sum_range_succ_shift (F : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, F (i + 1) = ∑ i ∈ Icc 1 n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- The weights vanish beyond the current count. -/
theorem onlineQRateWeight_eq_zero_of_lt {H N i : ℕ} (h : N < i) : onlineQRateWeight H N i = 0 := by
  unfold onlineQRateWeight
  rw [if_neg (by omega), if_neg (by omega)]

/-- Sum of a function of visit number truncated at `n`: extra visits contribute nothing. -/
theorem sum_range_le_of_vanish (F : ℕ → ℝ) (hF0 : ∀ i, 0 ≤ F i) (n m : ℕ)
    (hF : ∀ i, n ≤ i → F i = 0) : ∑ i ∈ range m, F i ≤ ∑ i ∈ range n, F i := by
  rcases le_or_gt m n with hmn | hmn
  · exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hmn) fun i _ _ ↦ hF0 i
  · rw [← sum_range_add_sum_Ico _ hmn.le]
    have : ∑ i ∈ Ico n m, F i = 0 := sum_eq_zero fun i hi ↦ hF i (mem_Ico.1 hi).1
    rw [this, add_zero]

/-- Rate-weighted penalty `β_n = Σ_{i=1}^n η_i^n b_i` for `b_i = c/√i`: `c/√n ≤ β_n ≤ 2c/√n`. -/
theorem beta_bounds {H : ℕ} (hH : 0 < H) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) :
    c / Real.sqrt n ≤ ∑ i ∈ Icc 1 n, onlineQRateWeight H n i * (c / Real.sqrt i) ∧
      ∑ i ∈ Icc 1 n, onlineQRateWeight H n i * (c / Real.sqrt i) ≤ 2 * c / Real.sqrt n := by
  have h := onlineQRateWeight_sqrt_sum_bounds H n hH hn
  have e : ∑ i ∈ Icc 1 n, onlineQRateWeight H n i * (c / Real.sqrt i) =
      c * ∑ i ∈ Icc 1 n, onlineQRateWeight H n i / Real.sqrt i := by
    rw [mul_sum]; refine sum_congr rfl fun i _ ↦ ?_; ring
  rw [e]
  constructor
  · calc c / Real.sqrt n = c * (1 / Real.sqrt n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h.1 hc
  · calc _ ≤ c * (2 / Real.sqrt n) := mul_le_mul_of_nonneg_left h.2 hc
      _ = 2 * c / Real.sqrt n := by ring

end StatisticalRL.LCBQFinite
