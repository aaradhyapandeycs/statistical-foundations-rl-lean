import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Weighted Assouad lemma (averaged form) and finite two-point testing tools

Generic finite-sum statements (used for the finite-horizon minimax lower bound).
Laws are given by their atom weights on a finite observation space `Ω`; no integrals appear.

* `assouad_weighted_sum`: the averaged weighted Assouad lemma. For a hypercube `Fin m → Bool` of
  laws `p σ`, decoders `d x j`, nonnegative weights `w j`, and a lower bound `θ` on every
  coordinate-flip test-error sum, `∑_σ ∑_x p σ x · ∑_j w_j 1[d x j ≠ σ j] ≥ 2^m (θ/2) ∑_j w_j`.
* `reverse_markov_sum`: for a `[−∞, W]`-valued variable `Z` and a probability vector `p`,
  `E Z ≤ tW + (1−t) W · P(Z ≥ tW)`.
* `bhattacharyya_sq_le_test_error`: Le Cam's inequality, the test-error sum of any test is at
  least `(∑_x √(p x q x))² / 2`.
* `sum_sqrt_prod_eq_prod_sum`: the Bhattacharyya coefficient of product laws factorizes.
* `bernoulli_bhattacharyya_ge`: a two-point Bhattacharyya lower bound.
-/

open Finset
open scoped BigOperators

namespace StatisticalRL.Assouad

section Flip

variable {m : ℕ}

/-- Flip the `j`th coordinate of a hypercube vertex. -/
def flipAt (j : Fin m) (σ : Fin m → Bool) : Fin m → Bool := Function.update σ j (!σ j)

@[simp] theorem flipAt_self (j : Fin m) (σ : Fin m → Bool) : flipAt j σ j = !σ j := by
  simp [flipAt]

theorem flipAt_of_ne {j k : Fin m} (h : k ≠ j) (σ : Fin m → Bool) : flipAt j σ k = σ k := by
  simp [flipAt, Function.update_of_ne h]

theorem flipAt_flipAt (j : Fin m) (σ : Fin m → Bool) : flipAt j (flipAt j σ) = σ := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · rw [flipAt_of_ne h, flipAt_of_ne h]

theorem flipAt_involutive (j : Fin m) : Function.Involutive (flipAt j) := flipAt_flipAt j

/-- The coordinate flip as a permutation of the hypercube. -/
def flipPerm (j : Fin m) : Equiv.Perm (Fin m → Bool) := (flipAt_involutive j).toPerm _

end Flip

section Assouad

variable {Ω : Type*} [Fintype Ω] {m : ℕ}

/-- **Weighted Assouad lemma, averaged form.** If for every coordinate `j` and every vertex `σ`
with `σ j = false` the test `x ↦ d x j` has error sum
`P_σ(d_j = true) + P_{σ^{(j)}}(d_j = false) ≥ θ`, then the hypercube sum of the expected weighted
Hamming losses is at least `2^m (θ/2) ∑_j w_j`. Nonnegativity of the atoms is not needed. -/
theorem assouad_weighted_sum (p : (Fin m → Bool) → Ω → ℝ) (w : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ w j) (d : Ω → Fin m → Bool) (θ : ℝ)
    (htest : ∀ j σ, σ j = false →
      θ ≤ (∑ x, p σ x * (if d x j = true then 1 else 0)) +
        ∑ x, p (flipAt j σ) x * (if d x j = false then 1 else 0)) :
    (2 : ℝ) ^ m * (θ / 2) * ∑ j, w j ≤
      ∑ σ, ∑ x, p σ x * ∑ j, w j * (if d x j ≠ σ j then 1 else 0) := by
  -- Error of the `j`th test under `σ`.
  set e : Fin m → (Fin m → Bool) → ℝ :=
    fun j σ ↦ ∑ x, p σ x * (if d x j ≠ σ j then 1 else 0) with he
  have hpair : ∀ j σ, θ ≤ e j σ + e j (flipAt j σ) := by
    have key : ∀ j σ, σ j = false → θ ≤ e j σ + e j (flipAt j σ) := by
      intro j σ hσ
      have h := htest j σ hσ
      have h1 : e j σ = ∑ x, p σ x * (if d x j = true then 1 else 0) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hσ]; cases d x j <;> simp
      have h2 : e j (flipAt j σ) = ∑ x, p (flipAt j σ) x * (if d x j = false then 1 else 0) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [flipAt_self, hσ]; cases d x j <;> simp
      rw [h1, h2]; exact h
    intro j σ
    cases hσ : σ j
    · exact key j σ hσ
    · have hτ : flipAt j σ j = false := by simp [hσ]
      have := key j (flipAt j σ) hτ
      rw [flipAt_flipAt] at this
      linarith
  have hsum : ∀ j, (2 : ℝ) ^ m * (θ / 2) ≤ ∑ σ, e j σ := by
    intro j
    have hcomp : ∑ σ, e j (flipAt j σ) = ∑ σ, e j σ :=
      Equiv.sum_comp (flipPerm j) (e j)
    have hge : (∑ _σ : Fin m → Bool, θ) ≤ ∑ σ, (e j σ + e j (flipAt j σ)) :=
      Finset.sum_le_sum fun σ _ ↦ hpair j σ
    rw [Finset.sum_add_distrib, hcomp, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul] at hge
    push_cast at hge
    linarith
  have hrhs : ∑ σ, ∑ x, p σ x * ∑ j, w j * (if d x j ≠ σ j then 1 else 0) =
      ∑ j, w j * ∑ σ, e j σ := by
    simp_rw [he, Finset.mul_sum]
    calc _ = ∑ σ, ∑ j, ∑ x, w j * (p σ x * (if d x j ≠ σ j then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl fun σ _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
          ring
      _ = _ := Finset.sum_comm
  rw [hrhs, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by
    have := mul_le_mul_of_nonneg_left (hsum j) (hw j)
    linarith

end Assouad

section ReverseMarkov

variable {Ω : Type*} [Fintype Ω]

/-- **Reverse Markov inequality** for a variable bounded above by `W`, in finite-sum form:
`E Z ≤ tW + (1 − t) W · P(tW ≤ Z)` (any real `t`, `W`). -/
theorem reverse_markov_sum (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (Z : Ω → ℝ) (W t : ℝ) (hZ : ∀ x, Z x ≤ W) :
    ∑ x, p x * Z x ≤ t * W + (1 - t) * W * ∑ x, p x * (if t * W ≤ Z x then 1 else 0) := by
  have hpt : ∀ x, Z x ≤ t * W + (1 - t) * W * (if t * W ≤ Z x then 1 else 0) := by
    intro x
    split_ifs with h
    · have := hZ x; linarith
    · push_neg at h; linarith
  calc ∑ x, p x * Z x
      ≤ ∑ x, p x * (t * W + (1 - t) * W * (if t * W ≤ Z x then 1 else 0)) :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hpt x) (hp x)
    _ = (∑ x, p x) * (t * W) + (1 - t) * W * ∑ x, p x * (if t * W ≤ Z x then 1 else 0) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        ring
    _ = _ := by rw [hsum, one_mul]

end ReverseMarkov

section Hellinger

variable {Ω : Type*} [Fintype Ω]

/-- **Le Cam's inequality** (finite form). For probability vectors `p, q` and any test `T`, the
error sum `P(T = true) + Q(T = false)` is at least `(∑_x √(p x q x))² / 2`. -/
theorem bhattacharyya_sq_le_test_error (p q : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) (T : Ω → Bool) :
    (∑ x, Real.sqrt (p x * q x)) ^ 2 / 2 ≤
      (∑ x, p x * (if T x = true then 1 else 0)) + ∑ x, q x * (if T x = false then 1 else 0) := by
  have hmin : ∑ x, min (p x) (q x) ≤
      (∑ x, p x * (if T x = true then 1 else 0)) + ∑ x, q x * (if T x = false then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    cases T x <;> simp
  have hsq : ∀ x, Real.sqrt (p x * q x) =
      Real.sqrt (min (p x) (q x)) * Real.sqrt (max (p x) (q x)) := by
    intro x
    rw [← Real.sqrt_mul (le_min (hp x) (hq x)), min_mul_max]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x ↦ Real.sqrt (min (p x) (q x))) (fun x ↦ Real.sqrt (max (p x) (q x)))
  simp only [Real.sq_sqrt (le_min (hp _) (hq _)),
    Real.sq_sqrt (le_trans (hp _) (le_max_left _ _))] at hcs
  simp_rw [← hsq] at hcs
  have hmax : ∑ x, max (p x) (q x) ≤ 2 := by
    calc ∑ x, max (p x) (q x) ≤ ∑ x, (p x + q x) :=
          Finset.sum_le_sum fun x _ ↦ max_le (by linarith [hq x]) (by linarith [hp x])
      _ = 2 := by rw [Finset.sum_add_distrib, hps, hqs]; norm_num
  have hminnn : 0 ≤ ∑ x, min (p x) (q x) :=
    Finset.sum_nonneg fun x _ ↦ le_min (hp x) (hq x)
  have : (∑ x, Real.sqrt (p x * q x)) ^ 2 ≤ 2 * ∑ x, min (p x) (q x) := by
    calc _ ≤ (∑ x, min (p x) (q x)) * ∑ x, max (p x) (q x) := hcs
      _ ≤ (∑ x, min (p x) (q x)) * 2 := mul_le_mul_of_nonneg_left hmax hminnn
      _ = _ := by ring
  linarith

/-- The square root of a finite product of nonnegative reals is the product of square roots. -/
theorem sqrt_prod_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.sqrt_mul (hf a (Finset.mem_insert_self a s)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- The Bhattacharyya coefficient of finite product laws is the product of the coordinate
coefficients. -/
theorem sum_sqrt_prod_eq_prod_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a b : ι → κ → ℝ) (ha : ∀ i y, 0 ≤ a i y) (hb : ∀ i y, 0 ≤ b i y) :
    ∑ x : ι → κ, Real.sqrt ((∏ i, a i (x i)) * ∏ i, b i (x i)) =
      ∏ i, ∑ y, Real.sqrt (a i y * b i y) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.prod_mul_distrib, sqrt_prod_eq _ _ fun i _ ↦ mul_nonneg (ha i _) (hb i _)]

/-- Two-point lower bound: for `x, y ≥ 0` with `x + y > 0`,
`√(xy) ≥ (x + y)/2 − (x − y)² / (2 (x + y))`. -/
theorem sqrt_mul_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x + y) :
    (x + y) / 2 - (x - y) ^ 2 / (2 * (x + y)) ≤ Real.sqrt (x * y) := by
  set u := Real.sqrt x with hu
  set v := Real.sqrt y with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg x
  have hv0 : 0 ≤ v := Real.sqrt_nonneg y
  have hux : u ^ 2 = x := Real.sq_sqrt hx
  have hvy : v ^ 2 = y := Real.sq_sqrt hy
  rw [Real.sqrt_mul hx, ← hu, ← hv, ← hux, ← hvy]
  rw [← hux, ← hvy] at hxy
  have hden : 0 < 2 * (u ^ 2 + v ^ 2) := by linarith
  rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have key : (u ^ 2 + v ^ 2) * (u - v) ^ 2 ≤ (u ^ 2 - v ^ 2) ^ 2 := by
    have : (u ^ 2 - v ^ 2) ^ 2 = (u - v) ^ 2 * (u + v) ^ 2 := by ring
    rw [this]
    have h2 : u ^ 2 + v ^ 2 ≤ (u + v) ^ 2 := by nlinarith [mul_nonneg hu0 hv0]
    nlinarith [sq_nonneg (u - v)]
  have h3 : (u ^ 2 + v ^ 2) - 2 * (u * v) ≤ (u ^ 2 - v ^ 2) ^ 2 / (u ^ 2 + v ^ 2) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [key]
  have h4 : (u ^ 2 - v ^ 2) ^ 2 / (2 * (u ^ 2 + v ^ 2)) * 2 =
      (u ^ 2 - v ^ 2) ^ 2 / (u ^ 2 + v ^ 2) := by
    field_simp
  nlinarith [h3, h4]

/-- Bhattacharyya coefficient of two Bernoulli-type two-point laws `(a, 1 − a)` and `(b, 1 − b)`:
if `a + b ≥ κ > 0` and `a + b ≤ 1`, then
`√(ab) + √((1−a)(1−b)) ≥ 1 − (a − b)² (1/κ + 1) / 2`. -/
theorem bernoulli_bhattacharyya_ge (a b κ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (hκ : 0 < κ) (hab : κ ≤ a + b) (hab1 : a + b ≤ 1) :
    1 - (a - b) ^ 2 * (1 / κ + 1) / 2 ≤ Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) := by
  have h1 := sqrt_mul_ge a b ha hb (by linarith)
  have h2 := sqrt_mul_ge (1 - a) (1 - b) (by linarith) (by linarith) (by linarith)
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have e1 : (a - b) ^ 2 / (2 * (a + b)) ≤ (a - b) ^ 2 / (2 * κ) :=
    div_le_div_of_nonneg_left hsq (by positivity) (by linarith)
  have e2 : (1 - a - (1 - b)) ^ 2 / (2 * (1 - a + (1 - b))) ≤ (a - b) ^ 2 / 2 := by
    have : (1 - a - (1 - b)) ^ 2 = (a - b) ^ 2 := by ring
    rw [this]
    exact div_le_div_of_nonneg_left hsq (by norm_num) (by linarith)
  have e3 : (a - b) ^ 2 * (1 / κ + 1) / 2 = (a - b) ^ 2 / (2 * κ) + (a - b) ^ 2 / 2 := by
    field_simp
  have e4 : (a + b) / 2 + (1 - a + (1 - b)) / 2 = 1 := by ring
  linarith

end Hellinger

end StatisticalRL.Assouad
