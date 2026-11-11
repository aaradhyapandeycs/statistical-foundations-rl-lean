import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Deterministic facts about time-varying learning rates (Theorem 4.7, case (i))

Scalar inputs for case (i) of `thm:LB-example-Q-generative`
(`chapters/generative_model_model_free.tex:969–982`, rates `η_t = 1/(1 + c_η(1-γ)t)`).

* products `Π_x(k,t) = ∏_{j=k+1}^t (1 - x η_j)` with the bounds
  `Π ≤ exp(-∑ x η_j) ≤ 1/(1 + ∑ x η_j)` and `Π ≥ exp(-(3/2) ∑ x η_j)` when `x η_j ≤ 1/3`;
* the square sums `S₂(t+1) = (1-η_{t+1})² S₂(t) + η_{t+1}²`, `S₄(t+1) = (1-η_{t+1})⁴ S₄(t) + η_{t+1}⁴`
  (the second and fourth powers of the Q-learning weights `η_k ∏_{j=k+1}^t (1-η_j)`, summed over
  `k ≤ t`), with `S₂(t) ≤ η_t`, `S₄(t) ≤ η_t² S₂(t)` under the weight condition
  `(1-η_{t+1}) η_t ≤ η_{t+1}` and `S₂(t) ≥ η_t/2` when moreover `η` is antitone and `η_1 ≥ 1/2`;
* the rescaled linear schedule `1/(1 + D t)`: range, monotonicity, the weight condition iff
  `D ≤ 1`, and harmonic-sum bounds.
-/

open scoped BigOperators
namespace StatisticalRL.QLearning

/-! ### Products -/

/-- `Π_x(k,t) = ∏_{j ∈ (k,t]} (1 - x η_j)`. -/
noncomputable def qLbvProd (η : ℕ → ℝ) (x : ℝ) (k t : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ioc k t, (1 - x * η j)

theorem qLbvProd_self (η : ℕ → ℝ) (x : ℝ) (k : ℕ) : qLbvProd η x k k = 1 := by
  simp [qLbvProd]

theorem qLbvProd_succ (η : ℕ → ℝ) (x : ℝ) (k t : ℕ) (hk : k ≤ t) :
    qLbvProd η x k (t + 1) = (1 - x * η (t + 1)) * qLbvProd η x k t := by
  unfold qLbvProd
  rw [Finset.prod_Ioc_succ_top hk, mul_comm]

theorem qLbvProd_nonneg (η : ℕ → ℝ) (x : ℝ) (k t : ℕ)
    (h : ∀ j, x * η j ≤ 1) : 0 ≤ qLbvProd η x k t :=
  Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (h j)

/-- `Π ≤ exp(-∑ x η_j)`. -/
theorem qLbvProd_le_exp (η : ℕ → ℝ) (x : ℝ) (k t : ℕ) (h1 : ∀ j, x * η j ≤ 1) :
    qLbvProd η x k t ≤ Real.exp (-∑ j ∈ Finset.Ioc k t, x * η j) := by
  unfold qLbvProd
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod (fun j _ ↦ sub_nonneg.mpr (h1 j))
    (fun j _ ↦ Real.one_sub_le_exp_neg _)

/-- `Π ≤ 1/(1 + ∑ x η_j)`. -/
theorem qLbvProd_le_inv (η : ℕ → ℝ) (x : ℝ) (k t : ℕ) (h0 : ∀ j, 0 ≤ x * η j)
    (h1 : ∀ j, x * η j ≤ 1) :
    qLbvProd η x k t ≤ 1 / (1 + ∑ j ∈ Finset.Ioc k t, x * η j) := by
  have hs : 0 ≤ ∑ j ∈ Finset.Ioc k t, x * η j := Finset.sum_nonneg fun j _ ↦ h0 j
  refine (qLbvProd_le_exp η x k t h1).trans ?_
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by linarith)]
  linarith [Real.add_one_le_exp (∑ j ∈ Finset.Ioc k t, x * η j)]

/-- `1 - y ≥ exp(-(3/2) y)` for `0 ≤ y ≤ 1/3`. -/
theorem qLbv_exp_le_one_sub (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1 / 3) :
    Real.exp (-(3 / 2 * y)) ≤ 1 - y := by
  have hpos : 0 < 1 - y := by linarith
  have hlog : -(3 / 2 * y) ≤ Real.log (1 - y) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : (1 - y)⁻¹ ≤ 1 + 3 / 2 * y := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    linarith
  calc Real.exp (-(3 / 2 * y)) ≤ Real.exp (Real.log (1 - y)) := Real.exp_le_exp.mpr hlog
    _ = 1 - y := Real.exp_log hpos

/-- `Π ≥ exp(-(3/2) ∑ x η_j)` when every factor has `0 ≤ x η_j ≤ 1/3`. -/
theorem qLbvProd_ge_exp (η : ℕ → ℝ) (x : ℝ) (k t : ℕ) (h0 : ∀ j, 0 ≤ x * η j)
    (h1 : ∀ j, x * η j ≤ 1 / 3) :
    Real.exp (-(3 / 2 * ∑ j ∈ Finset.Ioc k t, x * η j)) ≤ qLbvProd η x k t := by
  unfold qLbvProd
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod (fun j _ ↦ (Real.exp_pos _).le)
    (fun j _ ↦ qLbv_exp_le_one_sub _ (h0 j) (h1 j))

/-! ### Square sums of the weights -/

/-- `S₂(0) = 0`, `S₂(t+1) = (1-η_{t+1})² S₂(t) + η_{t+1}²`. -/
noncomputable def qLbvSq2 (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η (t + 1)) ^ 2 * qLbvSq2 η t + η (t + 1) ^ 2

/-- `S₄(0) = 0`, `S₄(t+1) = (1-η_{t+1})⁴ S₄(t) + η_{t+1}⁴`. -/
noncomputable def qLbvSq4 (η : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η (t + 1)) ^ 4 * qLbvSq4 η t + η (t + 1) ^ 4

theorem qLbvSq2_nonneg (η : ℕ → ℝ) (t : ℕ) : 0 ≤ qLbvSq2 η t := by
  induction t with
  | zero => simp [qLbvSq2]
  | succ t ih => simp only [qLbvSq2]; positivity

/-- `S₂(t) ≤ η_t` under the weight condition `(1-η_{t+1}) η_t ≤ η_{t+1}` (`(A3)`). -/
theorem qLbvSq2_le (η : ℕ → ℝ) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hstep : ∀ t, (1 - η (t + 1)) * η t ≤ η (t + 1)) (t : ℕ) : qLbvSq2 η t ≤ η t := by
  induction t with
  | zero => simp only [qLbvSq2]; exact (hη 0).1
  | succ t ih =>
    simp only [qLbvSq2]
    have h1 := hη (t + 1)
    have ha : 0 ≤ 1 - η (t + 1) := by linarith
    have e1 : (1 - η (t + 1)) ^ 2 * qLbvSq2 η t ≤ (1 - η (t + 1)) ^ 2 * η t :=
      mul_le_mul_of_nonneg_left ih (sq_nonneg _)
    have e2 : (1 - η (t + 1)) * ((1 - η (t + 1)) * η t) ≤ (1 - η (t + 1)) * η (t + 1) :=
      mul_le_mul_of_nonneg_left (hstep t) ha
    nlinarith

/-- `S₄(t) ≤ η_t² S₂(t)` under the weight condition (`(A3)`: every weight is `≤ η_t`). -/
theorem qLbvSq4_le (η : ℕ → ℝ) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hstep : ∀ t, (1 - η (t + 1)) * η t ≤ η (t + 1)) (t : ℕ) :
    qLbvSq4 η t ≤ η t ^ 2 * qLbvSq2 η t := by
  induction t with
  | zero => simp [qLbvSq4, qLbvSq2]
  | succ t ih =>
    simp only [qLbvSq4, qLbvSq2]
    have h1 := hη (t + 1)
    have h0 := hη t
    have ha : 0 ≤ 1 - η (t + 1) := by linarith
    have hS := qLbvSq2_nonneg η t
    have hw : ((1 - η (t + 1)) * η t) ^ 2 ≤ η (t + 1) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg ha h0.1) (hstep t) 2
    have e1 : (1 - η (t + 1)) ^ 4 * qLbvSq4 η t ≤ (1 - η (t + 1)) ^ 4 * (η t ^ 2 * qLbvSq2 η t) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have e2 : (1 - η (t + 1)) ^ 4 * (η t ^ 2 * qLbvSq2 η t) =
        ((1 - η (t + 1)) * η t) ^ 2 * ((1 - η (t + 1)) ^ 2 * qLbvSq2 η t) := by ring
    have e3 : ((1 - η (t + 1)) * η t) ^ 2 * ((1 - η (t + 1)) ^ 2 * qLbvSq2 η t) ≤
        η (t + 1) ^ 2 * ((1 - η (t + 1)) ^ 2 * qLbvSq2 η t) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    have e4 : η (t + 1) ^ 2 * ((1 - η (t + 1)) ^ 2 * qLbvSq2 η t + η (t + 1) ^ 2) =
        η (t + 1) ^ 2 * ((1 - η (t + 1)) ^ 2 * qLbvSq2 η t) + η (t + 1) ^ 4 := by ring
    rw [e4]
    linarith

/-- `S₂(t) ≥ η_t/2` for `t ≥ 1` when `η` is antitone on `[1,∞)` and `η_1 ≥ 1/2` (`(A4)`). -/
theorem qLbvSq2_ge (η : ℕ → ℝ) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hanti : ∀ t, 1 ≤ t → η (t + 1) ≤ η t) (h1 : 1 / 2 ≤ η 1) (t : ℕ) (ht : 1 ≤ t) :
    η t / 2 ≤ qLbvSq2 η t := by
  induction t, ht using Nat.le_induction with
  | base =>
    simp only [qLbvSq2, zero_add, mul_zero]
    have := (hη 1).1
    nlinarith
  | succ t ht ih =>
    simp only [qLbvSq2]
    have hb := hη (t + 1)
    have hdec := hanti t ht
    have e1 : (1 - η (t + 1)) ^ 2 * (η (t + 1) / 2) ≤ (1 - η (t + 1)) ^ 2 * qLbvSq2 η t :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    nlinarith [sq_nonneg (η (t + 1)), mul_nonneg hb.1 (sq_nonneg (η (t + 1)))]

/-! ### The rescaled linear schedule -/

/-- The rescaled linear rate `1/(1 + D t)` (case (i) with `D = c_η (1-γ)`). -/
theorem qLbvRate_pos (D : ℝ) (hD : 0 ≤ D) (t : ℕ) : 0 < 1 / (1 + D * t) := by positivity

theorem qLbvRate_le_one (D : ℝ) (hD : 0 ≤ D) (t : ℕ) : 1 / (1 + D * t) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have : 0 ≤ D * t := by positivity
  linarith

theorem qLbvRate_bounds (D : ℝ) (hD : 0 ≤ D) (t : ℕ) :
    0 ≤ 1 / (1 + D * t) ∧ 1 / (1 + D * t) ≤ 1 :=
  ⟨(qLbvRate_pos D hD t).le, qLbvRate_le_one D hD t⟩

theorem qLbvRate_anti (D : ℝ) (hD : 0 ≤ D) (t t' : ℕ) (h : t ≤ t') :
    1 / (1 + D * t') ≤ 1 / (1 + D * t) := by
  have ht : (t : ℝ) ≤ t' := by exact_mod_cast h
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem qLbvRate_le_inv (D : ℝ) (hD : 0 < D) (t : ℕ) (ht : 1 ≤ t) :
    1 / (1 + D * t) ≤ 1 / D * (1 / (t : ℝ)) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-- The weight condition `(1 - η_{t+1}) η_t ≤ η_{t+1}` holds for `1/(1+Dt)` when `D ≤ 1`. -/
theorem qLbvRate_step (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1) (t : ℕ) :
    (1 - 1 / (1 + D * ((t + 1 : ℕ) : ℝ))) * (1 / (1 + D * t)) ≤ 1 / (1 + D * ((t + 1 : ℕ) : ℝ)) := by
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have ha : 0 < 1 + D * t := by positivity
  have hb : 0 < 1 + D * ((t + 1 : ℕ) : ℝ) := by positivity
  push_cast at hb ⊢
  rw [one_sub_div hb.ne', div_mul_div_comm, div_le_div_iff₀ (by positivity) hb]
  have : (1 + D * (t + 1) - 1) * 1 * (1 + D * (t + 1)) ≤ 1 * ((1 + D * (t + 1)) * (1 + D * t)) := by
    have e : (1 + D * (t + 1) - 1) * 1 = D * (t + 1) := by ring
    rw [e, one_mul]
    have : D * (t + 1) ≤ 1 + D * t := by nlinarith
    nlinarith
  linarith

theorem qLbvRate_one_ge_half (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1) :
    1 / 2 ≤ 1 / (1 + D * ((1 : ℕ) : ℝ)) := by
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-! ### Harmonic sums -/

theorem qLbv_sum_inv_Ioc_zero (T : ℕ) :
    ∑ j ∈ Finset.Ioc 0 T, (1 / (j : ℝ)) ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  rw [show Finset.Ioc 0 T = Finset.Icc 1 T from (Finset.Icc_succ_left_eq_Ioc 0 T).symm]
  simpa [one_div] using h

theorem qLbv_sum_inv_Ioc_one (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.Ioc 1 T, (1 / (j : ℝ)) ≤ Real.log T := by
  have h := qLbv_sum_inv_Ioc_zero T
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hT, Nat.Ioc_succ_singleton] at h
  simp at h
  simpa [one_div] using h

/-- `∑_{j=1}^T 1/(1+Dj) ≤ (1 + log T)/D`. -/
theorem qLbvRate_sum_zero (D : ℝ) (hD : 0 < D) (T : ℕ) :
    ∑ j ∈ Finset.Ioc 0 T, 1 / (1 + D * j) ≤ 1 / D * (1 + Real.log T) := by
  calc ∑ j ∈ Finset.Ioc 0 T, 1 / (1 + D * j) ≤ ∑ j ∈ Finset.Ioc 0 T, 1 / D * (1 / (j : ℝ)) :=
        Finset.sum_le_sum fun j hj ↦ qLbvRate_le_inv D hD j (Finset.mem_Ioc.mp hj).1
    _ = 1 / D * ∑ j ∈ Finset.Ioc 0 T, (1 / (j : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 1 / D * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_left (qLbv_sum_inv_Ioc_zero T) (by positivity)

/-- `∑_{j=2}^T 1/(1+Dj) ≤ (log T)/D`. -/
theorem qLbvRate_sum_one (D : ℝ) (hD : 0 < D) (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.Ioc 1 T, 1 / (1 + D * j) ≤ 1 / D * Real.log T := by
  calc ∑ j ∈ Finset.Ioc 1 T, 1 / (1 + D * j) ≤ ∑ j ∈ Finset.Ioc 1 T, 1 / D * (1 / (j : ℝ)) :=
        Finset.sum_le_sum fun j hj ↦ qLbvRate_le_inv D hD j (by
          have := (Finset.mem_Ioc.mp hj).1; omega)
    _ = 1 / D * ∑ j ∈ Finset.Ioc 1 T, (1 / (j : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 1 / D * Real.log T :=
        mul_le_mul_of_nonneg_left (qLbv_sum_inv_Ioc_one T hT) (by positivity)

end StatisticalRL.QLearning
