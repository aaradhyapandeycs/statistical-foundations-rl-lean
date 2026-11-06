import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

import Formalization.Online.QLearning.RateWeightDefinitions

/-!
Proof helpers and source bounds for the online Q-learning rate weights in
`lemma:property_lr`. The source definitions live in the separate
definition-only `RateWeightDefinitions` module.
-/

namespace StatisticalRL.OnlineRL

open Finset Filter Topology

section Helpers

variable {H : ℕ}

lemma onlineQRate_denom_pos (hH : 0 < H) (i : ℕ) : (0 : ℝ) < (H : ℝ) + i := by
  have h1 : (0 : ℝ) < H := by exact_mod_cast hH
  have h2 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

lemma onlineQRate_pos (hH : 0 < H) (n : ℕ) : 0 < onlineQRate H n := by
  unfold onlineQRate
  have h := onlineQRate_denom_pos hH n
  have h1 : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  exact div_pos h1 h

lemma onlineQRate_one (hH : 0 < H) : onlineQRate H 1 = 1 := by
  have h : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  unfold onlineQRate
  rw [Nat.cast_one]
  exact div_self h.ne'

lemma one_sub_onlineQRate (hH : 0 < H) (i : ℕ) :
    1 - onlineQRate H i = ((i : ℝ) - 1) / ((H : ℝ) + i) := by
  have h := onlineQRate_denom_pos hH i
  unfold onlineQRate
  field_simp
  ring

lemma one_sub_onlineQRate_nonneg (hH : 0 < H) {i : ℕ} (hi : 1 ≤ i) :
    0 ≤ 1 - onlineQRate H i := by
  rw [one_sub_onlineQRate hH]
  have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  exact div_nonneg (by linarith) (onlineQRate_denom_pos hH i).le

lemma onlineQRateWeight_of_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    onlineQRateWeight H N n =
      onlineQRate H n * ∏ i ∈ Finset.Icc (n + 1) N, (1 - onlineQRate H i) := by
  unfold onlineQRateWeight
  rw [if_neg (by omega), if_pos hnN]

lemma onlineQRateWeight_self {N : ℕ} (hN : 1 ≤ N) :
    onlineQRateWeight H N N = onlineQRate H N := by
  rw [onlineQRateWeight_of_le hN le_rfl,
    Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self N), prod_empty, mul_one]

lemma onlineQRateWeight_succ {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    onlineQRateWeight H (N + 1) n = (1 - onlineQRate H (N + 1)) * onlineQRateWeight H N n := by
  rw [onlineQRateWeight_of_le hn (by omega), onlineQRateWeight_of_le hn hnN,
    prod_Icc_succ_top (by omega : n + 1 ≤ N + 1)]
  ring

lemma onlineQRateWeight_nonneg (hH : 0 < H) (N n : ℕ) : 0 ≤ onlineQRateWeight H N n := by
  unfold onlineQRateWeight
  split_ifs with h0 h1
  · exact prod_nonneg fun i hi => one_sub_onlineQRate_nonneg hH (mem_Icc.1 hi).1
  · refine mul_nonneg (onlineQRate_pos hH n).le (prod_nonneg fun i hi => ?_)
    exact one_sub_onlineQRate_nonneg hH (by have := (mem_Icc.1 hi).1; omega)
  · exact le_rfl

/-- One-step recursion of weighted sums (`η_n^{N+1} = (1-η_{N+1}) η_n^N`). -/
lemma onlineQRateWeight_sum_succ (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 (N + 1), onlineQRateWeight H (N + 1) n * f n =
      (1 - onlineQRate H (N + 1)) * ∑ n ∈ Icc 1 N, onlineQRateWeight H N n * f n
        + onlineQRate H (N + 1) * f (N + 1) := by
  rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), onlineQRateWeight_self (by omega : 1 ≤ N + 1),
    mul_sum]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  have hn' := mem_Icc.1 hn
  rw [onlineQRateWeight_succ hn'.1 hn'.2]
  ring

/-- Normalization `eq:sum-eta-n-N` for `N > 0`. -/
lemma onlineQRateWeight_sum_eq_one (hH : 0 < H) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, onlineQRateWeight H N n = 1 := by
  induction N, hN using Nat.le_induction with
  | base => rw [Icc_self, sum_singleton, onlineQRateWeight_self le_rfl, onlineQRate_one hH]
  | succ N hN ih =>
    have h := onlineQRateWeight_sum_succ (H := H) N (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h, ih]
    ring

/-- Pointwise bound `η_n^N ≤ (H+1)/(H+N)` used in the author proof. -/
lemma onlineQRateWeight_le (hH : 0 < H) {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    onlineQRateWeight H N n ≤ ((H : ℝ) + 1) / ((H : ℝ) + N) := by
  induction N, hnN using Nat.le_induction with
  | base => rw [onlineQRateWeight_self hn]; exact le_rfl
  | succ N hnN ih =>
    rw [onlineQRateWeight_succ hn hnN, one_sub_onlineQRate hH]
    have hd1 := onlineQRate_denom_pos hH N
    have hd2 := onlineQRate_denom_pos hH (N + 1)
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hc : (0 : ℝ) ≤ (((N + 1 : ℕ) : ℝ) - 1) / ((H : ℝ) + ((N + 1 : ℕ) : ℝ)) := by
      apply div_nonneg _ hd2.le
      push_cast; linarith
    calc (((N + 1 : ℕ) : ℝ) - 1) / ((H : ℝ) + ((N + 1 : ℕ) : ℝ)) * onlineQRateWeight H N n
        ≤ (((N + 1 : ℕ) : ℝ) - 1) / ((H : ℝ) + ((N + 1 : ℕ) : ℝ)) *
            (((H : ℝ) + 1) / ((H : ℝ) + N)) := mul_le_mul_of_nonneg_left ih hc
      _ ≤ ((H : ℝ) + 1) / ((H : ℝ) + ((N + 1 : ℕ) : ℝ)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hd2 hd1) hd2]
        push_cast
        have hp : 0 ≤ ((H : ℝ) + 1) * ((H : ℝ) + (N + 1)) * (H : ℝ) := by positivity
        nlinarith [hp]

end Helpers

/-- `eq:properties-learning-rates-sqrt`, in product form. -/
lemma onlineQRateWeight_sqrt_sum_bounds_aux {H : ℕ} (hH : 0 < H) {N : ℕ} (hN : 1 ≤ N) :
    (Real.sqrt N)⁻¹ ≤ ∑ n ∈ Icc 1 N, onlineQRateWeight H N n * (Real.sqrt n)⁻¹ ∧
      ∑ n ∈ Icc 1 N, onlineQRateWeight H N n * (Real.sqrt n)⁻¹ ≤ 2 * (Real.sqrt N)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Icc_self, sum_singleton, onlineQRateWeight_self le_rfl, onlineQRate_one hH]
    norm_num
  | succ N hN ih =>
    obtain ⟨ihl, ihu⟩ := ih
    rw [onlineQRateWeight_sum_succ (H := H) N (fun n => (Real.sqrt n)⁻¹),
      one_sub_onlineQRate hH]
    set T := ∑ n ∈ Icc 1 N, onlineQRateWeight H N n * (Real.sqrt n)⁻¹ with hT
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hr : onlineQRate H (N + 1) = ((H : ℝ) + 1) / ((H : ℝ) + ((N : ℝ) + 1)) := by
      unfold onlineQRate; push_cast; ring
    have hc : (((N + 1 : ℕ) : ℝ) - 1) / ((H : ℝ) + ((N + 1 : ℕ) : ℝ)) =
        (N : ℝ) / ((H : ℝ) + ((N : ℝ) + 1)) := by push_cast; ring
    have hs_eq : Real.sqrt ((N + 1 : ℕ) : ℝ) = Real.sqrt ((N : ℝ) + 1) := by push_cast; rfl
    rw [hr, hc, hs_eq]
    set s := Real.sqrt ((N : ℝ) + 1) with hs
    set t := Real.sqrt (N : ℝ) with ht
    set D := (H : ℝ) + ((N : ℝ) + 1) with hD
    have hDpos : 0 < D := by rw [hD]; linarith
    have htpos : 0 < t := Real.sqrt_pos.2 (by linarith)
    have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hts : t ≤ s := Real.sqrt_le_sqrt (by linarith)
    have ht2 : t ^ 2 = N := Real.sq_sqrt (by linarith)
    have hs2 : s ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by linarith)
    constructor
    · -- lower bound
      have hsplit : s⁻¹ = (N : ℝ) / D * s⁻¹ + ((H : ℝ) + 1) / D * s⁻¹ := by
        rw [← add_mul, ← add_div, hD]
        rw [show (N : ℝ) + ((H : ℝ) + 1) = (H : ℝ) + ((N : ℝ) + 1) by ring,
          div_self (by linarith), one_mul]
      calc s⁻¹ = (N : ℝ) / D * s⁻¹ + ((H : ℝ) + 1) / D * s⁻¹ := hsplit
        _ ≤ (N : ℝ) / D * T + ((H : ℝ) + 1) / D * s⁻¹ := by
          gcongr
          exact le_trans (inv_anti₀ htpos hts) ihl
    · -- upper bound
      have e1 : (N : ℝ) / D * (2 * t⁻¹) = 2 * t / D := by
        rw [← ht2]; field_simp
      have e2 : 2 * t / D + ((H : ℝ) + 1) / D * s⁻¹ = (2 * t * s + ((H : ℝ) + 1)) / (D * s) := by
        field_simp
      have e3 : 2 * s⁻¹ = (2 * D) / (D * s) := by
        field_simp
      calc (N : ℝ) / D * T + ((H : ℝ) + 1) / D * s⁻¹
          ≤ (N : ℝ) / D * (2 * t⁻¹) + ((H : ℝ) + 1) / D * s⁻¹ := by gcongr
        _ = (2 * t * s + ((H : ℝ) + 1)) / (D * s) := by rw [e1, e2]
        _ ≤ (2 * D) / (D * s) := by
          gcongr
          have hmul : t * s ≤ s * s := mul_le_mul_of_nonneg_right hts hspos.le
          rw [hD]
          nlinarith [hmul, hs2, hH1]
        _ = 2 * s⁻¹ := e3.symm

/-- `eq:properties-learning-rates-sqrt`. -/
theorem onlineQRateWeight_sqrt_sum_bounds (H N : ℕ) (hH : 0 < H) (hN : 0 < N) :
    1 / Real.sqrt (N : ℝ) ≤
        (∑ n ∈ Finset.Icc 1 N, onlineQRateWeight H N n / Real.sqrt (n : ℝ)) ∧
      (∑ n ∈ Finset.Icc 1 N, onlineQRateWeight H N n / Real.sqrt (n : ℝ)) ≤
        2 / Real.sqrt (N : ℝ) := by
  have h := onlineQRateWeight_sqrt_sum_bounds_aux (H := H) hH (N := N) (by omega)
  simp only [div_eq_mul_inv, one_mul]
  exact h

/-- `eq:properties-learning-rates-square`. -/
theorem onlineQRateWeight_sq_sum_le (H N : ℕ) (hH : 0 < H) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 N, (onlineQRateWeight H N n) ^ 2) ≤ 2 * (H : ℝ) / (N : ℝ) := by
  have hM : ∀ n ∈ Icc 1 N, (onlineQRateWeight H N n) ^ 2 ≤
      onlineQRateWeight H N n * (((H : ℝ) + 1) / ((H : ℝ) + N)) := by
    intro n hn
    have h := mem_Icc.1 hn
    rw [sq]
    exact mul_le_mul_of_nonneg_left (onlineQRateWeight_le hH h.1 h.2)
      (onlineQRateWeight_nonneg hH N n)
  have h1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (∑ n ∈ Icc 1 N, (onlineQRateWeight H N n) ^ 2)
      ≤ ∑ n ∈ Icc 1 N, onlineQRateWeight H N n * (((H : ℝ) + 1) / ((H : ℝ) + N)) :=
        sum_le_sum hM
    _ = ((H : ℝ) + 1) / ((H : ℝ) + N) := by
        rw [← sum_mul, onlineQRateWeight_sum_eq_one hH (by omega), one_mul]
    _ ≤ 2 * (H : ℝ) / (N : ℝ) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ N), sq_nonneg (H : ℝ)]

section Tail

variable {H n : ℕ}

lemma onlineQRateWeight_tail_succ (hH : 0 < H) (hn : 1 ≤ n) (K : ℕ) :
    ((H : ℝ) + n + K + 1) * onlineQRateWeight H (n + (K + 1)) n =
      ((n : ℝ) + K) * onlineQRateWeight H (n + K) n := by
  rw [← add_assoc, onlineQRateWeight_succ hn (by omega), one_sub_onlineQRate hH]
  have hd := onlineQRate_denom_pos hH (n + K + 1)
  push_cast at hd ⊢
  field_simp
  ring

/-- Telescoped partial sums of the tail series (author proof, `a_N` telescope). -/
lemma onlineQRateWeight_tail_partial (hH : 0 < H) (hn : 1 ≤ n) (K : ℕ) :
    ∑ k ∈ range K, onlineQRateWeight H (n + k) n =
      (1 + 1 / (H : ℝ)) - ((H : ℝ) + n + K) / H * onlineQRateWeight H (n + K) n := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  induction K with
  | zero =>
    rw [range_zero, sum_empty, Nat.add_zero, onlineQRateWeight_self hn]
    unfold onlineQRate
    have hd := onlineQRate_denom_pos hH n
    push_cast
    field_simp
    ring
  | succ K ih =>
    rw [sum_range_succ, ih]
    have hrec := onlineQRateWeight_tail_succ hH hn K
    have e : ((H : ℝ) + n + ((K + 1 : ℕ) : ℝ)) / H * onlineQRateWeight H (n + (K + 1)) n =
        ((n : ℝ) + K) / H * onlineQRateWeight H (n + K) n := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      congr 1
      push_cast
      rw [show (H : ℝ) + n + (K + 1) = (H : ℝ) + n + K + 1 by ring, hrec]
    rw [e]
    field_simp
    ring

/-- Polynomial decay of the tail weights: `(n+K)(n+K+1) η_n^{n+K} ≤ n(n+1)`. -/
lemma onlineQRateWeight_tail_decay (hH : 0 < H) (hn : 1 ≤ n) (K : ℕ) :
    ((n : ℝ) + K) * ((n : ℝ) + K + 1) * onlineQRateWeight H (n + K) n ≤ (n : ℝ) * (n + 1) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  induction K with
  | zero =>
    rw [Nat.add_zero, onlineQRateWeight_self hn]
    unfold onlineQRate
    have hd := onlineQRate_denom_pos hH n
    simp only [Nat.cast_zero, add_zero]
    have hle : ((H : ℝ) + 1) / ((H : ℝ) + n) ≤ 1 := by
      rw [div_le_one hd]; linarith
    have hpos : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
    calc (n : ℝ) * ((n : ℝ) + 1) * (((H : ℝ) + 1) / ((H : ℝ) + n))
        ≤ (n : ℝ) * ((n : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left hle hpos
      _ = (n : ℝ) * (n + 1) := by ring
  | succ K ih =>
    have hrec := onlineQRateWeight_tail_succ hH hn K
    have hw := onlineQRateWeight_nonneg hH (n + K) n
    have hw' := onlineQRateWeight_nonneg hH (n + (K + 1)) n
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    push_cast
    -- (n+K+1)(n+K+2) w' ≤ (H+n+K+1) (n+K+1) w' = (n+K+1)(n+K) w ≤ ...
    have h1 : ((n : ℝ) + (K + 1)) * ((n : ℝ) + (K + 1) + 1) * onlineQRateWeight H (n + (K + 1)) n ≤
        ((n : ℝ) + K + 1) * (((H : ℝ) + n + K + 1) * onlineQRateWeight H (n + (K + 1)) n) := by
      have : ((n : ℝ) + (K + 1) + 1) ≤ (H : ℝ) + n + K + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_right this hw',
        mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + K + 1) hw']
    rw [hrec] at h1
    nlinarith [h1, ih, hw]

/-- The remainder `(H+n+K)/H · η_n^{n+K}` tends to zero. -/
lemma onlineQRateWeight_tail_remainder_tendsto (hH : 0 < H) (hn : 1 ≤ n) :
    Tendsto (fun K : ℕ => ((H : ℝ) + n + K) / H * onlineQRateWeight H (n + K) n)
      atTop (𝓝 0) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set C : ℝ := ((H : ℝ) + 1) * (n * (n + 1)) / H with hC
  have hbound : ∀ K : ℕ, ((H : ℝ) + n + K) / H * onlineQRateWeight H (n + K) n ≤
      C * (1 / ((K : ℝ) + 1)) := by
    intro K
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hw := onlineQRateWeight_nonneg hH (n + K) n
    have hdec := onlineQRateWeight_tail_decay hH hn K
    -- (H+n+K)(K+1) ≤ (H+1)(n+K)(n+K+1)
    have hfac : ((H : ℝ) + n + K) * ((K : ℝ) + 1) ≤
        ((H : ℝ) + 1) * (((n : ℝ) + K) * ((n : ℝ) + K + 1)) := by
      nlinarith [mul_nonneg hHpos.le hK0, mul_nonneg (sub_nonneg.2 hn1) hK0,
        mul_nonneg hHpos.le (sub_nonneg.2 hn1), mul_nonneg (mul_nonneg hHpos.le hK0) hK0,
        mul_nonneg (mul_nonneg hHpos.le hK0) (sub_nonneg.2 hn1)]
    have hkey : ((H : ℝ) + n + K) * onlineQRateWeight H (n + K) n * ((K : ℝ) + 1) ≤
        ((H : ℝ) + 1) * (n * (n + 1)) := by
      calc ((H : ℝ) + n + K) * onlineQRateWeight H (n + K) n * ((K : ℝ) + 1)
          = ((H : ℝ) + n + K) * ((K : ℝ) + 1) * onlineQRateWeight H (n + K) n := by ring
        _ ≤ ((H : ℝ) + 1) * (((n : ℝ) + K) * ((n : ℝ) + K + 1)) *
              onlineQRateWeight H (n + K) n := mul_le_mul_of_nonneg_right hfac hw
        _ = ((H : ℝ) + 1) * (((n : ℝ) + K) * ((n : ℝ) + K + 1) *
              onlineQRateWeight H (n + K) n) := by ring
        _ ≤ ((H : ℝ) + 1) * ((n : ℝ) * (n + 1)) :=
              mul_le_mul_of_nonneg_left hdec (by positivity)
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    calc ((H : ℝ) + n + K) / H * onlineQRateWeight H (n + K) n
        = ((H : ℝ) + n + K) * onlineQRateWeight H (n + K) n * ((K : ℝ) + 1) / H *
            (1 / ((K : ℝ) + 1)) := by
          field_simp
      _ ≤ ((H : ℝ) + 1) * (n * (n + 1)) / H * (1 / ((K : ℝ) + 1)) := by
          gcongr
      _ = C * (1 / ((K : ℝ) + 1)) := by rw [hC]
  have hnonneg : ∀ K : ℕ, 0 ≤ ((H : ℝ) + n + K) / H * onlineQRateWeight H (n + K) n := by
    intro K
    exact mul_nonneg (div_nonneg (by positivity) hHpos.le) (onlineQRateWeight_nonneg hH _ _)
  have hlim : Tendsto (fun K : ℕ => C * (1 / ((K : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  exact squeeze_zero hnonneg hbound hlim

end Tail

/-- `eq:properties-learning-rates-tail`, with summability proved. -/
theorem onlineQRateWeight_tail_sum (H n : ℕ) (hH : 0 < H) (hn : 0 < n) :
    Summable (fun k : ℕ => onlineQRateWeight H (n + k) n) ∧
      (∑' k : ℕ, onlineQRateWeight H (n + k) n) = 1 + 1 / (H : ℝ) := by
  have hn' : 1 ≤ n := hn
  have hsum : HasSum (fun k : ℕ => onlineQRateWeight H (n + k) n) (1 + 1 / (H : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => onlineQRateWeight_nonneg hH _ _)]
    have h := (tendsto_const_nhds (x := (1 + 1 / (H : ℝ)))).sub
      (onlineQRateWeight_tail_remainder_tendsto hH hn')
    rw [sub_zero] at h
    refine h.congr fun K => ?_
    exact (onlineQRateWeight_tail_partial hH hn' K).symm
  exact ⟨hsum.summable, hsum.tsum_eq⟩

end StatisticalRL.OnlineRL
