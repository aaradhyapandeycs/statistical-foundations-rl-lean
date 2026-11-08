import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Fin.Basic

/-!
# Adaptive product lemma, Markov consequence and finite union bound

On `Fin K → α` with history-dependent kernels `p k x a` (depending on `x j`, `j < k`) and
nonnegative factors `Y k x` (depending on `x j`, `j ≤ k`) whose conditional mean is at most one,
`∑_x ∏_k p k x (x k) · ∏_k Y k x ≤ 1` (`adaptive_prod_le`). This is the adaptive generalization of
`StatisticalRL.LCBQFinite.lemmaG` (`OfflineRL/FiniteLCBQ/Supermart.lean`), proved by the same
`Fin.snoc` induction. Also: total mass one (`adaptive_prod_sum_eq_one`), the Markov consequence
(`adaptive_markov`) and a finite union bound (`union_bound_sum`).

These declarations were first proved for corrected Theorem 7.12 in
`Formalization/Ch7Rest/VPOAdaptive712.lean`, which now re-exports them under their original names.
-/

namespace StatisticalRL.AdaptiveKL

open Finset

variable {α : Type*} [Fintype α]

/-- Adaptive product lemma (L8). -/
theorem adaptive_prod_le : ∀ (K : ℕ) (p : Fin K → (Fin K → α) → α → ℝ)
    (Yf : Fin K → (Fin K → α) → ℝ),
    (∀ k x a, 0 ≤ p k x a) →
    (∀ k x y, (∀ j : Fin K, j < k → x j = y j) → p k x = p k y) →
    (∀ k x, 0 ≤ Yf k x) →
    (∀ k x y, (∀ j : Fin K, j ≤ k → x j = y j) → Yf k x = Yf k y) →
    (∀ k x, ∑ a, p k x a * Yf k (Function.update x k a) ≤ 1) →
    ∑ x : Fin K → α, (∏ k, p k x (x k)) * ∏ k, Yf k x ≤ 1 := by
  intro K
  induction K with
  | zero => intro p Yf _ _ _ _ _; simp
  | succ K ih =>
    intro p Yf hp0 hpdep hY0 hYdep hstep
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
    · simp
    let e := Fin.snocEquiv (fun _ : Fin (K + 1) ↦ α)
    rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm]
    let p' : Fin K → (Fin K → α) → α → ℝ := fun k y ↦ p k.castSucc (Fin.snoc y a₀)
    let Y' : Fin K → (Fin K → α) → ℝ := fun k y ↦ Yf k.castSucc (Fin.snoc y a₀)
    have hp' : ∀ k (y : Fin K → α) a, p k.castSucc (Fin.snoc y a) = p' k y := by
      intro k y a
      refine hpdep _ _ _ fun j hj ↦ ?_
      have hj' : j ≠ Fin.last K := fun h ↦ by
        subst h; exact absurd hj (not_lt.2 (Fin.castSucc_lt_last k).le)
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
      simp
    have hY' : ∀ k (y : Fin K → α) a, Yf k.castSucc (Fin.snoc y a) = Y' k y := by
      intro k y a
      refine hYdep _ _ _ fun j hj ↦ ?_
      have hj' : j ≠ Fin.last K := fun h ↦ by
        subst h; exact absurd hj (not_le.2 (Fin.castSucc_lt_last k))
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
      simp
    have hplast : ∀ (y : Fin K → α) a, p (Fin.last K) (Fin.snoc y a) = p (Fin.last K) (Fin.snoc y a₀) := by
      intro y a
      refine hpdep _ _ _ fun j hj ↦ ?_
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hj)
      simp
    have hpdep' : ∀ k x y, (∀ j : Fin K, j < k → x j = y j) → p' k x = p' k y := by
      intro k x y hxy
      refine hpdep _ _ _ fun j hj ↦ ?_
      by_cases hj' : j = Fin.last K
      · subst hj'; exact absurd hj (not_lt.2 (Fin.castSucc_lt_last k).le)
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
        simp only [Fin.snoc_castSucc]
        exact hxy i (Fin.castSucc_lt_castSucc_iff.1 hj)
    have hYdep' : ∀ k x y, (∀ j : Fin K, j ≤ k → x j = y j) → Y' k x = Y' k y := by
      intro k x y hxy
      refine hYdep _ _ _ fun j hj ↦ ?_
      by_cases hj' : j = Fin.last K
      · subst hj'; simp
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
        simp only [Fin.snoc_castSucc]
        exact hxy i (Fin.castSucc_le_castSucc_iff.1 hj)
    have hstep' : ∀ k x, ∑ a, p' k x a * Y' k (Function.update x k a) ≤ 1 := by
      intro k x
      have := hstep k.castSucc (Fin.snoc x a₀)
      refine le_trans (le_of_eq ?_) this
      refine sum_congr rfl fun a _ ↦ ?_
      simp only [p', Y', Fin.snoc_update]
    have hih := ih p' Y' (fun k x a ↦ hp0 _ _ _) hpdep' (fun k x ↦ hY0 _ _) hYdep' hstep'
    refine le_trans (sum_le_sum fun y _ ↦ ?_) hih
    have hlast := hstep (Fin.last K) (Fin.snoc y a₀)
    simp only [Fin.update_snoc_last] at hlast
    have hP : 0 ≤ (∏ k, p' k y (y k)) * ∏ k, Y' k y :=
      mul_nonneg (prod_nonneg fun k _ ↦ hp0 _ _ _) (prod_nonneg fun k _ ↦ hY0 _ _)
    have hfac : ∀ a, (∏ k, p k (Fin.snoc (α := fun _ ↦ α) y a)
        (Fin.snoc (α := fun _ ↦ α) y a k)) * ∏ k, Yf k (Fin.snoc (α := fun _ ↦ α) y a) =
        ((∏ k, p' k y (y k)) * ∏ k, Y' k y) *
          (p (Fin.last K) (Fin.snoc y a₀) a * Yf (Fin.last K) (Fin.snoc y a)) := by
      intro a
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hp', hY', hplast]
      ring
    show ∑ a, (∏ k, p k (Fin.snoc (α := fun _ ↦ α) y a) (Fin.snoc (α := fun _ ↦ α) y a k)) *
        ∏ k, Yf k (Fin.snoc (α := fun _ ↦ α) y a) ≤ _
    rw [sum_congr rfl fun a _ ↦ hfac a, ← mul_sum]
    calc _ ≤ ((∏ k, p' k y (y k)) * ∏ k, Y' k y) * 1 := mul_le_mul_of_nonneg_left hlast hP
      _ = _ := mul_one _

/-- Total mass one of the adaptive product law. -/
theorem adaptive_prod_sum_eq_one [Nonempty α] : ∀ (K : ℕ) (p : Fin K → (Fin K → α) → α → ℝ),
    (∀ k x y, (∀ j : Fin K, j < k → x j = y j) → p k x = p k y) →
    (∀ k x, ∑ a, p k x a = 1) →
    ∑ x : Fin K → α, ∏ k, p k x (x k) = 1 := by
  intro K
  induction K with
  | zero => intro p _ _; simp
  | succ K ih =>
    intro p hpdep hsum
    obtain ⟨a₀⟩ := ‹Nonempty α›
    let e := Fin.snocEquiv (fun _ : Fin (K + 1) ↦ α)
    rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm]
    let p' : Fin K → (Fin K → α) → α → ℝ := fun k y ↦ p k.castSucc (Fin.snoc y a₀)
    have hp' : ∀ k (y : Fin K → α) a, p k.castSucc (Fin.snoc y a) = p' k y := by
      intro k y a
      refine hpdep _ _ _ fun j hj ↦ ?_
      have hj' : j ≠ Fin.last K := fun h ↦ by
        subst h; exact absurd hj (not_lt.2 (Fin.castSucc_lt_last k).le)
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
      simp
    have hplast : ∀ (y : Fin K → α) a, p (Fin.last K) (Fin.snoc y a) = p (Fin.last K) (Fin.snoc y a₀) := by
      intro y a
      refine hpdep _ _ _ fun j hj ↦ ?_
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hj)
      simp
    have hpdep' : ∀ k x y, (∀ j : Fin K, j < k → x j = y j) → p' k x = p' k y := by
      intro k x y hxy
      refine hpdep _ _ _ fun j hj ↦ ?_
      by_cases hj' : j = Fin.last K
      · subst hj'; exact absurd hj (not_lt.2 (Fin.castSucc_lt_last k).le)
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hj'
        simp only [Fin.snoc_castSucc]
        exact hxy i (Fin.castSucc_lt_castSucc_iff.1 hj)
    have hsum' : ∀ k x, ∑ a, p' k x a = 1 := fun k x ↦ hsum _ _
    have hih := ih p' hpdep' hsum'
    rw [← hih]
    refine sum_congr rfl fun y _ ↦ ?_
    have hfac : ∀ a, ∏ k, p k (Fin.snoc (α := fun _ ↦ α) y a) (Fin.snoc (α := fun _ ↦ α) y a k) =
        (∏ k, p' k y (y k)) * p (Fin.last K) (Fin.snoc y a₀) a := by
      intro a
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hp', hplast]
    show ∑ a, ∏ k, p k (Fin.snoc (α := fun _ ↦ α) y a) (Fin.snoc (α := fun _ ↦ α) y a k) = _
    rw [sum_congr rfl fun a _ ↦ hfac a, ← mul_sum, hsum, mul_one]

/-- Markov consequence: `P(∏ Y ≥ c) ≤ 1/c`. -/
theorem adaptive_markov (K : ℕ) (p : Fin K → (Fin K → α) → α → ℝ)
    (Yf : Fin K → (Fin K → α) → ℝ)
    (hp0 : ∀ k x a, 0 ≤ p k x a)
    (hpdep : ∀ k x y, (∀ j : Fin K, j < k → x j = y j) → p k x = p k y)
    (hY0 : ∀ k x, 0 ≤ Yf k x)
    (hYdep : ∀ k x y, (∀ j : Fin K, j ≤ k → x j = y j) → Yf k x = Yf k y)
    (hstep : ∀ k x, ∑ a, p k x a * Yf k (Function.update x k a) ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∑ x : Fin K → α, (∏ k, p k x (x k)) * (if c ≤ ∏ k, Yf k x then 1 else 0) ≤ 1 / c := by
  have hA := adaptive_prod_le K p Yf hp0 hpdep hY0 hYdep hstep
  calc _ ≤ ∑ x : Fin K → α, (∏ k, p k x (x k)) * ((∏ k, Yf k x) / c) := by
        refine sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun k _ ↦ hp0 _ _ _)
        split_ifs with h
        · rw [le_div_iff₀ hc, one_mul]; exact h
        · exact div_nonneg (prod_nonneg fun k _ ↦ hY0 _ _) hc.le
    _ = (∑ x : Fin K → α, (∏ k, p k x (x k)) * ∏ k, Yf k x) / c := by
        rw [sum_div]; refine sum_congr rfl fun x _ ↦ by ring
    _ ≤ 1 / c := div_le_div_of_nonneg_right hA hc.le

/-- Finite union bound for indicator sums with nonnegative weights. -/
theorem union_bound_sum {β ι : Type*} [Fintype β] (w : β → ℝ) (hw : ∀ x, 0 ≤ w x)
    (s : Finset ι) (P : ι → β → Prop) [∀ i x, Decidable (P i x)] [∀ x, Decidable (∃ i ∈ s, P i x)] :
    ∑ x, w x * (if ∃ i ∈ s, P i x then 1 else 0) ≤
      ∑ i ∈ s, ∑ x, w x * (if P i x then 1 else 0) := by
  rw [sum_comm]
  refine sum_le_sum fun x _ ↦ ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hw x)
  split_ifs with h
  · obtain ⟨i, hi, hPi⟩ := h
    calc (1 : ℝ) = if P i x then 1 else 0 := by rw [if_pos hPi]
      _ ≤ _ := single_le_sum (f := fun i ↦ if P i x then (1 : ℝ) else 0)
          (fun j _ ↦ by dsimp only; split_ifs <;> norm_num) hi
  · exact sum_nonneg fun j _ ↦ by split_ifs <;> norm_num

end StatisticalRL.AdaptiveKL
