import Formalization.Probability.AdaptiveKLDefinitions
import Formalization.Probability.AdaptiveProduct
import Formalization.Probability.ExpQuadraticBound

/-!
# Exponential tail bounds for finite sequential laws

For the finite sequential law `seqLaw κ N` of `AdaptiveKLDefinitions`:

* `seqLaw_prob_eq_prod`: the probability of a history is the product of the step-kernel
  probabilities along its prefixes.
* `seqLaw_exp_tail`: if `f k` depends only on the entries `≤ k` and its conditional exponential
  moment given every prefix is at most one, then `P(L ≤ ∑_k f_k) ≤ e^{-L}`. This is a
  specialisation of `adaptive_markov` (`RLHF/VPO/Adaptive.lean`).
* `seqPrefix k x`: the length-`k` prefix of a history.
* One-step lemmas: `sum_exp_sub_sq_le_one` (mean-zero increments with `|X| ≤ 1`, Freedman-type)
  and `sum_exp_sub_two_mul_le_one` (increments in `[0,1]`, multiplicative).
* `seqLaw_freedman_tail`, `seqLaw_multiplicative_tail`: the corresponding tail bounds for
  adaptive increments.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.AdaptiveKL

variable {Z : Type*} [Fintype Z]

/-- The length-`k` prefix of a history `x : Fin N → Z`, for `k < N`. -/
def seqPrefix {N : ℕ} (k : Fin N) (x : Fin N → Z) : Fin k → Z :=
  fun j => x (Fin.castLE k.isLt.le j)

omit [Fintype Z] in
theorem seqPrefix_congr {N : ℕ} (k : Fin N) {x y : Fin N → Z} (h : ∀ j : Fin N, j < k → x j = y j) :
    seqPrefix k x = seqPrefix k y := by
  funext j
  exact h _ (by simp [Fin.lt_def])

omit [Fintype Z] in
theorem seqPrefix_update_self {N : ℕ} (k : Fin N) (x : Fin N → Z) (z : Z) :
    seqPrefix k (Function.update x k z) = seqPrefix k x :=
  seqPrefix_congr k fun _ hj => Function.update_of_ne (ne_of_lt hj) _ _

/-- The sequential law is the product of the step kernels along the prefixes. -/
theorem seqLaw_prob_eq_prod (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) :
    ∀ (N : ℕ) (x : Fin N → Z), (seqLaw κ N).prob x = ∏ k : Fin N, (κ k (seqPrefix k x)).prob (x k) := by
  intro N
  induction N with
  | zero => intro x; simp [seqLaw_zero_prob]
  | succ N ih =>
    intro x
    rw [seqLaw_succ_prob, ih, Fin.prod_univ_castSucc]
    rfl

/-- Exponential tail bound for adaptive sums (specialisation of `adaptive_markov`). -/
theorem seqLaw_exp_tail (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) (N : ℕ)
    (f : Fin N → (Fin N → Z) → ℝ)
    (hdep : ∀ k x y, (∀ j : Fin N, j ≤ k → x j = y j) → f k x = f k y)
    (hstep : ∀ (k : Fin N) x, ∑ z, (κ k (seqPrefix k x)).prob z * Real.exp (f k (Function.update x k z)) ≤ 1)
    (L : ℝ) :
    ∑ x, (seqLaw κ N).prob x * (if L ≤ ∑ k, f k x then 1 else 0) ≤ Real.exp (-L) := by
  have hM := adaptive_markov N (fun k x z => (κ k (seqPrefix k x)).prob z)
    (fun k x => Real.exp (f k x)) (fun k x z => (κ k (seqPrefix k x)).prob_nonneg z)
    (fun k x y hxy => by dsimp only; rw [seqPrefix_congr k hxy]) (fun k x => (Real.exp_pos _).le)
    (fun k x y hxy => by dsimp only; rw [hdep k x y hxy]) hstep (Real.exp_pos L)
  have hc : ∀ x : Fin N → Z, (if Real.exp L ≤ ∏ k, Real.exp (f k x) then (1 : ℝ) else 0) =
      if L ≤ ∑ k, f k x then 1 else 0 := by
    intro x
    rw [← Real.exp_sum]
    simp only [Real.exp_le_exp]
  simp only [hc] at hM
  rw [Real.exp_neg, ← one_div]
  refine le_trans (le_of_eq ?_) hM
  refine sum_congr rfl fun x _ => ?_
  rw [seqLaw_prob_eq_prod]

/-- Freedman-type one-step bound: for a probability vector `w` and a mean-zero `X` with
`|X| ≤ 1`, `∑ w e^{X − ∑ w X²} ≤ 1`. -/
theorem sum_exp_sub_sq_le_one {ι : Type*} [Fintype ι] (w X : ι → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hw1 : ∑ z, w z = 1) (hmean : ∑ z, w z * X z = 0) (hX : ∀ z, |X z| ≤ 1) :
    ∑ z, w z * Real.exp (X z - ∑ z', w z' * X z' ^ 2) ≤ 1 := by
  set V := ∑ z', w z' * X z' ^ 2
  have h1 : ∑ z, w z * Real.exp (X z - V) = Real.exp (-V) * ∑ z, w z * Real.exp (X z) := by
    rw [mul_sum]; refine sum_congr rfl fun z _ => ?_
    rw [sub_eq_add_neg, Real.exp_add]; ring
  have h2 : ∑ z, w z * Real.exp (X z) ≤ 1 + V := by
    calc ∑ z, w z * Real.exp (X z) ≤ ∑ z, w z * (1 + X z + X z ^ 2) :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (exp_le_one_add_add_sq (hX z)) (hw z)
      _ = ∑ z, w z + ∑ z, w z * X z + V := by
          rw [← sum_add_distrib, ← sum_add_distrib]; refine sum_congr rfl fun z _ => by ring
      _ = 1 + V := by rw [hw1, hmean, add_zero]
  rw [h1]
  calc Real.exp (-V) * ∑ z, w z * Real.exp (X z) ≤ Real.exp (-V) * Real.exp V :=
        mul_le_mul_of_nonneg_left (h2.trans (by linarith [Real.add_one_le_exp V]))
          (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Multiplicative one-step bound: for a probability vector `w` and `Y ∈ [0,1]`,
`∑ w e^{Y − 2 ∑ w Y} ≤ 1`. -/
theorem sum_exp_sub_two_mul_le_one {ι : Type*} [Fintype ι] (w Y : ι → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hw1 : ∑ z, w z = 1) (hY0 : ∀ z, 0 ≤ Y z) (hY1 : ∀ z, Y z ≤ 1) :
    ∑ z, w z * Real.exp (Y z - 2 * ∑ z', w z' * Y z') ≤ 1 := by
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ z', w z' * Y z' := ⟨_, rfl⟩
  rw [← hE]
  have h1 : ∑ z, w z * Real.exp (Y z - 2 * E) = Real.exp (-(2 * E)) * ∑ z, w z * Real.exp (Y z) := by
    rw [mul_sum]; refine sum_congr rfl fun z _ => ?_
    rw [sub_eq_add_neg, Real.exp_add]; ring
  have hy : ∀ z, Real.exp (Y z) ≤ 1 + 2 * Y z := by
    intro z
    have h := exp_le_one_add_add_sq (x := Y z) (by rw [abs_of_nonneg (hY0 z)]; exact hY1 z)
    nlinarith [hY0 z, hY1 z]
  have h2 : ∑ z, w z * Real.exp (Y z) ≤ 1 + 2 * E := by
    calc ∑ z, w z * Real.exp (Y z) ≤ ∑ z, w z * (1 + 2 * Y z) :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hy z) (hw z)
      _ = ∑ z, w z + 2 * ∑ z', w z' * Y z' := by
          rw [Finset.mul_sum, ← sum_add_distrib]; refine sum_congr rfl fun z _ => by ring
      _ = 1 + 2 * E := by rw [hw1, hE]
  rw [h1]
  calc Real.exp (-(2 * E)) * ∑ z, w z * Real.exp (Y z) ≤ Real.exp (-(2 * E)) * Real.exp (2 * E) :=
        mul_le_mul_of_nonneg_left (h2.trans (by linarith [Real.add_one_le_exp (2 * E)]))
          (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Freedman-type tail for adaptive mean-zero increments bounded by one: with
`X k x z` depending on `x` only through the entries before `k`, mean zero under the step kernel and
`|X| ≤ 1`, `P(L ≤ ∑_k (X_k(x_k) − E_k X_k²)) ≤ e^{-L}`. -/
theorem seqLaw_freedman_tail (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) (N : ℕ)
    (X : Fin N → (Fin N → Z) → Z → ℝ)
    (hdep : ∀ k x y, (∀ j : Fin N, j < k → x j = y j) → X k x = X k y)
    (hmean : ∀ (k : Fin N) x, ∑ z, (κ k (seqPrefix k x)).prob z * X k x z = 0)
    (hbd : ∀ k x z, |X k x z| ≤ 1) (L : ℝ) :
    ∑ x, (seqLaw κ N).prob x *
      (if L ≤ ∑ k, (X k x (x k) - ∑ z, (κ k (seqPrefix k x)).prob z * X k x z ^ 2) then 1 else 0) ≤
      Real.exp (-L) := by
  refine seqLaw_exp_tail κ N
    (fun k x => X k x (x k) - ∑ z, (κ k (seqPrefix k x)).prob z * X k x z ^ 2) ?_ ?_ L
  · intro k x y hxy
    have h1 : X k x = X k y := hdep k x y fun j hj => hxy j hj.le
    dsimp only
    rw [h1, hxy k le_rfl, seqPrefix_congr k fun j hj => hxy j hj.le]
  · intro k x
    have hfun : ∀ z, X k (Function.update x k z) = X k x :=
      fun z => hdep k _ _ fun j hj => Function.update_of_ne (ne_of_lt hj) _ _
    simp only [hfun, Function.update_self, seqPrefix_update_self]
    exact sum_exp_sub_sq_le_one _ _ (fun z => (κ k (seqPrefix k x)).prob_nonneg z)
      (κ k (seqPrefix k x)).sum_prob (hmean k x) (hbd k x)

/-- Multiplicative tail for adaptive increments in `[0,1]`:
`P(L ≤ ∑_k (Y_k(x_k) − 2 E_k Y_k)) ≤ e^{-L}`. -/
theorem seqLaw_multiplicative_tail (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) (N : ℕ)
    (Y : Fin N → (Fin N → Z) → Z → ℝ)
    (hdep : ∀ k x y, (∀ j : Fin N, j < k → x j = y j) → Y k x = Y k y)
    (hY0 : ∀ k x z, 0 ≤ Y k x z) (hY1 : ∀ k x z, Y k x z ≤ 1) (L : ℝ) :
    ∑ x, (seqLaw κ N).prob x *
      (if L ≤ ∑ k, (Y k x (x k) - 2 * ∑ z, (κ k (seqPrefix k x)).prob z * Y k x z) then 1 else 0) ≤
      Real.exp (-L) := by
  refine seqLaw_exp_tail κ N
    (fun k x => Y k x (x k) - 2 * ∑ z, (κ k (seqPrefix k x)).prob z * Y k x z) ?_ ?_ L
  · intro k x y hxy
    have h1 : Y k x = Y k y := hdep k x y fun j hj => hxy j hj.le
    dsimp only
    rw [h1, hxy k le_rfl, seqPrefix_congr k fun j hj => hxy j hj.le]
  · intro k x
    have hfun : ∀ z, Y k (Function.update x k z) = Y k x :=
      fun z => hdep k _ _ fun j hj => Function.update_of_ne (ne_of_lt hj) _ _
    simp only [hfun, Function.update_self, seqPrefix_update_self]
    exact sum_exp_sub_two_mul_le_one _ _ (fun z => (κ k (seqPrefix k x)).prob_nonneg z)
      (κ k (seqPrefix k x)).sum_prob (hY0 k x) (hY1 k x)

end StatisticalRL.AdaptiveKL
