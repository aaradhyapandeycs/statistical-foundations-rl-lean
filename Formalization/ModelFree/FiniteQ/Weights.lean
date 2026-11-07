import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Interval.Finset.Nat

/-! # Learning-rate weights for late iterations

For a start time `t₀` and `t₀ ≤ t`, the recursion `y_j = (1 - η_j) y_{j-1} + η_j z_j` (`t₀ < j ≤ t`)
unrolls to `y_t = Π_t y_{t₀} + Σ_{i ∈ (t₀,t]} η_i^{(t)} z_i` with
`Π_t = ∏_{j ∈ (t₀,t]} (1 - η_j)` and `η_i^{(t)} = η_i ∏_{j ∈ (i,t]} (1 - η_j)` (`def:eta-k-t`
restricted to late iterations; cf. `lemma:Q-step-size`, appendix :2539–2586). Everything here is
deterministic. -/

open Finset

namespace StatisticalRL.FiniteQLearning

/-- `Π_t = ∏_{j ∈ (t₀,t]} (1 - η_j)`. -/
noncomputable def tailProd (η : ℕ → ℝ) (t₀ t : ℕ) : ℝ := ∏ j ∈ Ioc t₀ t, (1 - η j)

/-- `η_i^{(t)} = η_i ∏_{j ∈ (i,t]} (1 - η_j)`. -/
noncomputable def weight (η : ℕ → ℝ) (i t : ℕ) : ℝ := η i * ∏ j ∈ Ioc i t, (1 - η j)

/-- The closed form `Π_t A + Σ_{i ∈ (t₀,t]} η_i^{(t)} z_i`. -/
noncomputable def unrolled (η : ℕ → ℝ) (t₀ t : ℕ) (A : ℝ) (z : ℕ → ℝ) : ℝ :=
  tailProd η t₀ t * A + ∑ i ∈ Ioc t₀ t, weight η i t * z i

/-- `∏_{j ∈ (t₀,t]} (1 - η_j / 2)`, used in the explicit super-solution. -/
noncomputable def halfProd (η : ℕ → ℝ) (t₀ t : ℕ) : ℝ := ∏ j ∈ Ioc t₀ t, (1 - η j / 2)

/-- Rates in `[0,1]` on the window `(t₀, t]`. -/
def UnitRates (η : ℕ → ℝ) (t₀ t : ℕ) : Prop := ∀ j, t₀ < j → j ≤ t → 0 ≤ η j ∧ η j ≤ 1

theorem UnitRates.mono {η : ℕ → ℝ} {t₀ t t' : ℕ} (h : UnitRates η t₀ t) (ht : t' ≤ t) :
    UnitRates η t₀ t' := fun j hj hj' ↦ h j hj (hj'.trans ht)

@[simp] theorem tailProd_self (η : ℕ → ℝ) (t₀ : ℕ) : tailProd η t₀ t₀ = 1 := by
  simp [tailProd]

@[simp] theorem halfProd_self (η : ℕ → ℝ) (t₀ : ℕ) : halfProd η t₀ t₀ = 1 := by
  simp [halfProd]

@[simp] theorem unrolled_self (η : ℕ → ℝ) (t₀ : ℕ) (A : ℝ) (z : ℕ → ℝ) :
    unrolled η t₀ t₀ A z = A := by
  simp [unrolled]

theorem tailProd_succ (η : ℕ → ℝ) {t₀ t : ℕ} (ht : t₀ ≤ t) :
    tailProd η t₀ (t + 1) = (1 - η (t + 1)) * tailProd η t₀ t := by
  rw [tailProd, tailProd, prod_Ioc_succ_top ht, mul_comm]

theorem halfProd_succ (η : ℕ → ℝ) {t₀ t : ℕ} (ht : t₀ ≤ t) :
    halfProd η t₀ (t + 1) = (1 - η (t + 1) / 2) * halfProd η t₀ t := by
  rw [halfProd, halfProd, prod_Ioc_succ_top ht, mul_comm]

theorem weight_succ (η : ℕ → ℝ) {i t : ℕ} (hi : i ≤ t) :
    weight η i (t + 1) = (1 - η (t + 1)) * weight η i t := by
  rw [weight, weight, prod_Ioc_succ_top hi]
  ring

@[simp] theorem weight_self (η : ℕ → ℝ) (t : ℕ) : weight η t t = η t := by
  simp [weight]

/-- The closed form obeys the one-step recursion. -/
theorem unrolled_succ (η : ℕ → ℝ) {t₀ t : ℕ} (ht : t₀ ≤ t) (A : ℝ) (z : ℕ → ℝ) :
    unrolled η t₀ (t + 1) A z = (1 - η (t + 1)) * unrolled η t₀ t A z + η (t + 1) * z (t + 1) := by
  rw [unrolled, unrolled, tailProd_succ η ht, sum_Ioc_succ_top ht, weight_self]
  have hs : ∑ i ∈ Ioc t₀ t, weight η i (t + 1) * z i =
      (1 - η (t + 1)) * ∑ i ∈ Ioc t₀ t, weight η i t * z i := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [weight_succ η (mem_Ioc.mp hi).2]
    ring
  rw [hs]
  ring

/-- Any solution of the recursion on `(t₀, t]` equals its closed form. -/
theorem eq_unrolled (η : ℕ → ℝ) (t₀ : ℕ) (y z : ℕ → ℝ) {t : ℕ} (ht : t₀ ≤ t)
    (hy : ∀ j, t₀ < j → j ≤ t → y j = (1 - η j) * y (j - 1) + η j * z j) :
    y t = unrolled η t₀ t (y t₀) z := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [hy (t + 1) (by omega) le_rfl, unrolled_succ η ht, Nat.add_sub_cancel,
      ih fun j hj hj' ↦ hy j hj (by omega)]

theorem tailProd_nonneg {η : ℕ → ℝ} {t₀ t : ℕ} (h : UnitRates η t₀ t) :
    0 ≤ tailProd η t₀ t :=
  prod_nonneg fun j hj ↦ by
    have := h j (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2
    linarith

theorem halfProd_nonneg {η : ℕ → ℝ} {t₀ t : ℕ} (h : UnitRates η t₀ t) :
    0 ≤ halfProd η t₀ t :=
  prod_nonneg fun j hj ↦ by
    have := h j (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2
    linarith

theorem weight_nonneg {η : ℕ → ℝ} {t₀ t i : ℕ} (h : UnitRates η t₀ t) (hi : i ∈ Ioc t₀ t) :
    0 ≤ weight η i t := by
  have hi' := mem_Ioc.mp hi
  refine mul_nonneg (h i hi'.1 hi'.2).1 (prod_nonneg fun j hj ↦ ?_)
  have hj' := mem_Ioc.mp hj
  have := h j (by omega) hj'.2
  linarith

theorem weight_le_rate {η : ℕ → ℝ} {t₀ t i : ℕ} (h : UnitRates η t₀ t) (hi : i ∈ Ioc t₀ t) :
    weight η i t ≤ η i := by
  have hi' := mem_Ioc.mp hi
  have hp : ∏ j ∈ Ioc i t, (1 - η j) ≤ 1 := by
    apply prod_le_one
    · intro j hj
      have hj' := mem_Ioc.mp hj
      have := h j (by omega) hj'.2
      linarith
    · intro j hj
      have hj' := mem_Ioc.mp hj
      have := h j (by omega) hj'.2
      linarith
  have := mul_le_mul_of_nonneg_left hp (h i hi'.1 hi'.2).1
  simpa [weight] using this

/-- `Π_t + Σ_{i ∈ (t₀,t]} η_i^{(t)} = 1`. -/
theorem tailProd_add_sum_weight (η : ℕ → ℝ) {t₀ t : ℕ} (ht : t₀ ≤ t) :
    tailProd η t₀ t + ∑ i ∈ Ioc t₀ t, weight η i t = 1 := by
  have h := eq_unrolled η t₀ (fun _ ↦ 1) (fun _ ↦ 1) ht (fun j _ _ ↦ by ring)
  simp only [unrolled, mul_one] at h
  exact h.symm

/-- Monotonicity of the closed form in the inputs. -/
theorem unrolled_mono {η : ℕ → ℝ} {t₀ t : ℕ} (h : UnitRates η t₀ t) {A A' : ℝ} {z z' : ℕ → ℝ}
    (hA : A ≤ A') (hz : ∀ i, t₀ < i → i ≤ t → z i ≤ z' i) :
    unrolled η t₀ t A z ≤ unrolled η t₀ t A' z' := by
  unfold unrolled
  apply add_le_add (mul_le_mul_of_nonneg_left hA (tailProd_nonneg h))
  apply sum_le_sum
  intro i hi
  have hi' := mem_Ioc.mp hi
  exact mul_le_mul_of_nonneg_left (hz i hi'.1 hi'.2) (weight_nonneg h hi)

/-- Sum of squared weights: if `η_i ≤ η̄` on `(t₀,t]`, then `Σ (η_i^{(t)})² ≤ η̄`. -/
theorem sum_weight_sq_le {η : ℕ → ℝ} {t₀ t : ℕ} (ht : t₀ ≤ t) (h : UnitRates η t₀ t) {ηbar : ℝ}
    (hbar0 : 0 ≤ ηbar) (hbar : ∀ i, t₀ < i → i ≤ t → η i ≤ ηbar) :
    ∑ i ∈ Ioc t₀ t, weight η i t ^ 2 ≤ ηbar := by
  have h1 : ∑ i ∈ Ioc t₀ t, weight η i t ^ 2 ≤ ∑ i ∈ Ioc t₀ t, ηbar * weight η i t := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_Ioc.mp hi
    have hw0 := weight_nonneg h hi
    have hw1 := (weight_le_rate h hi).trans (hbar i hi'.1 hi'.2)
    nlinarith
  rw [← mul_sum] at h1
  have hs := tailProd_add_sum_weight η ht
  have hp := tailProd_nonneg h
  nlinarith

/-- `1 - x ≤ exp (-x)` termwise: `∏ (1 - η_j/2) ≤ exp (-(Σ η_j)/2)`. -/
theorem halfProd_le_exp {η : ℕ → ℝ} {t₀ t : ℕ} (h : UnitRates η t₀ t) :
    halfProd η t₀ t ≤ Real.exp (-(∑ j ∈ Ioc t₀ t, η j) / 2) := by
  have : Real.exp (-(∑ j ∈ Ioc t₀ t, η j) / 2) = ∏ j ∈ Ioc t₀ t, Real.exp (-(η j / 2)) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [show ∀ j, -(η j / 2) = (-1 / 2) * η j from fun j ↦ by ring, ← mul_sum]
    ring
  rw [this, halfProd]
  apply prod_le_prod
  · intro j hj
    have hj' := mem_Ioc.mp hj
    have := h j hj'.1 hj'.2
    linarith
  · intro j _
    have := Real.add_one_le_exp (-(η j / 2))
    linarith

/-- Explicit super-solution of the comparison recursion: if `A ≤ 2G` and `G ≥ 0`, then
`Π_t A + Σ_i η_i^{(t)} G ∏_{(t₀,i]} (1 - η_j/2) ≤ 2G ∏_{(t₀,t]} (1 - η_j/2)`. -/
theorem unrolled_halfProd_le {η : ℕ → ℝ} {t₀ t : ℕ} (ht : t₀ ≤ t) (h : UnitRates η t₀ t)
    {A G : ℝ} (hG : 0 ≤ G) (hA : A ≤ 2 * G) :
    unrolled η t₀ t A (fun i ↦ G * halfProd η t₀ i) ≤ 2 * G * halfProd η t₀ t := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hA
  | succ t ht ih =>
    have ih' := ih (h.mono (Nat.le_succ t))
    rw [unrolled_succ η ht, halfProd_succ η ht]
    obtain ⟨h0, h1⟩ := h (t + 1) (by omega) le_rfl
    have hp := halfProd_nonneg (h.mono (Nat.le_succ t))
    have hGp : 0 ≤ G * halfProd η t₀ t := mul_nonneg hG hp
    have key : (1 - η (t + 1)) * unrolled η t₀ t A (fun i ↦ G * halfProd η t₀ i) ≤
        (1 - η (t + 1)) * (2 * G * halfProd η t₀ t) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    have hsq : 0 ≤ η (t + 1) ^ 2 * (G * halfProd η t₀ t) := mul_nonneg (sq_nonneg _) hGp
    nlinarith

end StatisticalRL.FiniteQLearning
