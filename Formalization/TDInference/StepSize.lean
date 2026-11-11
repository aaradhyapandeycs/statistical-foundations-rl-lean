import Formalization.TDInference.Definitions
import Formalization.Analysis.StepSizeCubeRoot

/-!
# The schedule `η_t = η₀ t^{-2/3}`: monotonicity, sums and slow variation

Elementary facts about the printed step size `stepSize η₀ t = η₀ t^{-2/3}` (`inference.tex:134`),
for use in second-moment and Polyak–Ruppert arguments. Everything is reduced to the cube root
`u_t = t^{1/3}`, for which `u_{t+1}^3 − u_t^3 = 1`:

* The generic cube-root facts are in `StepSizeCubeRoot.lean` (`StatisticalRL.Probability`).
* `stepSize_eq`: `η_t = η₀ / u_t²`; `invStepSize η₀ t = t^{2/3}/η₀` equals `1/η_t` for `t ≥ 1`
  (`invStepSize_eq_inv`) and is `0` at `t = 0`.
* `invStepSize_succ_sub_le`: `1/η_{t+1} − 1/η_t ≤ 1/(η₀ u_{t+1})` (all `t ≥ 0`, with the `t = 0`
  value `invStepSize η₀ 0 = 0`).
* `sum_range_stepSize_succ_le`: `∑_{t=1}^n η_t ≤ 3 η₀ n^{1/3}`.
* `stepSize_succ_le_stepSize`: `η_{t+1} ≤ η_t` for `t ≥ 1`.
* `stepSize_sub_succ_le`: slow variation `η_t − η_{t+1} ≤ (a/2) η_{t+1} η_t` once
  `(t+1)^{1/3} ≥ 2/(a η₀)`.
-/

open Finset

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

/-- `η_t = η₀ / u_t²`. -/
theorem stepSize_eq (η₀ : ℝ) (t : ℕ) : stepSize η₀ t = η₀ / natCubeRoot t ^ 2 := by
  rw [stepSize, Real.rpow_neg (Nat.cast_nonneg _), natCast_rpow_two_thirds_eq, div_eq_mul_inv]

theorem stepSize_pos {η₀ : ℝ} (h0 : 0 < η₀) {t : ℕ} (ht : 1 ≤ t) : 0 < stepSize η₀ t := by
  rw [stepSize_eq]; have := natCubeRoot_pos ht; positivity

theorem stepSize_nonneg {η₀ : ℝ} (h0 : 0 ≤ η₀) (t : ℕ) : 0 ≤ stepSize η₀ t :=
  mul_nonneg h0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem stepSize_le {η₀ : ℝ} (h0 : 0 ≤ η₀) {t : ℕ} (ht : 1 ≤ t) : stepSize η₀ t ≤ η₀ := by
  refine mul_le_of_le_one_right h0 (Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num))
  exact_mod_cast ht

/-- `η_{t'} ≤ η_t` for `1 ≤ t ≤ t'`. -/
theorem stepSize_anti {η₀ : ℝ} (h0 : 0 ≤ η₀) {t t' : ℕ} (ht : 1 ≤ t) (htt' : t ≤ t') :
    stepSize η₀ t' ≤ stepSize η₀ t := by
  rw [stepSize_eq, stepSize_eq]
  have h1 := natCubeRoot_pos ht
  have h2 := natCubeRoot_mono htt'
  exact div_le_div_of_nonneg_left h0 (by positivity) (pow_le_pow_left₀ h1.le h2 2)

theorem stepSize_succ_le_stepSize {η₀ : ℝ} (h0 : 0 ≤ η₀) {t : ℕ} (ht : 1 ≤ t) :
    stepSize η₀ (t + 1) ≤ stepSize η₀ t :=
  stepSize_anti h0 ht (Nat.le_succ t)

/-- `t^{2/3}/η₀`: equal to `1/η_t` for `t ≥ 1` and to `0` at `t = 0`. -/
noncomputable def invStepSize (η₀ : ℝ) (t : ℕ) : ℝ := natCubeRoot t ^ 2 / η₀

theorem invStepSize_zero (η₀ : ℝ) : invStepSize η₀ 0 = 0 := by
  simp [invStepSize, natCubeRoot]

theorem invStepSize_eq_inv {η₀ : ℝ} (h0 : 0 < η₀) {t : ℕ} (ht : 1 ≤ t) :
    invStepSize η₀ t = (stepSize η₀ t)⁻¹ := by
  have := natCubeRoot_pos ht
  rw [invStepSize, stepSize_eq]
  field_simp

theorem invStepSize_mono {η₀ : ℝ} (h0 : 0 < η₀) {s t : ℕ} (h : s ≤ t) :
    invStepSize η₀ s ≤ invStepSize η₀ t :=
  div_le_div_of_nonneg_right (pow_le_pow_left₀ (natCubeRoot_nonneg s) (natCubeRoot_mono h) 2) h0.le

/-- `1/η_{t+1} − 1/η_t ≤ 1/(η₀ u_{t+1})` (with `invStepSize η₀ 0 = 0`). -/
theorem invStepSize_succ_sub_le {η₀ : ℝ} (h0 : 0 < η₀) (t : ℕ) :
    invStepSize η₀ (t + 1) - invStepSize η₀ t ≤ 1 / (η₀ * natCubeRoot (t + 1)) := by
  have ha := natCubeRoot_pos (Nat.le_add_left 1 t)
  have h := sq_sub_sq_le_inv_of_cube_sub_eq_one
    (natCubeRoot_mono (Nat.le_succ t)) ha (natCubeRoot_succ_cube_sub t)
  rw [invStepSize, invStepSize, ← sub_div, div_le_div_iff₀ h0 (by positivity)]
  rw [le_div_iff₀ ha] at h
  nlinarith

/-- `∑_{t=1}^n η_t ≤ 3 η₀ n^{1/3}`. -/
theorem sum_range_stepSize_succ_le {η₀ : ℝ} (h0 : 0 ≤ η₀) (n : ℕ) :
    ∑ t ∈ range n, stepSize η₀ (t + 1) ≤ 3 * η₀ * natCubeRoot n := by
  have hterm : ∀ t ∈ range n, stepSize η₀ (t + 1) ≤
      3 * η₀ * (natCubeRoot (t + 1) - natCubeRoot t) := by
    intro t _
    have ha := natCubeRoot_pos (Nat.le_add_left 1 t)
    have h := inv_sq_le_three_mul_sub_of_cube_sub_eq_one (natCubeRoot_nonneg t)
      (natCubeRoot_mono (Nat.le_succ t)) ha (natCubeRoot_succ_cube_sub t)
    rw [stepSize_eq, div_eq_mul_one_div]
    have := mul_le_mul_of_nonneg_left h h0
    linarith
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← mul_sum, sum_range_sub (fun t ↦ natCubeRoot t)]
  simp [natCubeRoot]

/-- Slow variation: `η_t − η_{t+1} ≤ (a/2) η_{t+1} η_t` once `2/(a η₀) ≤ (t+1)^{1/3}`. -/
theorem stepSize_sub_succ_le {η₀ a : ℝ} (h0 : 0 < η₀) (ha : 0 < a) {t : ℕ} (ht : 1 ≤ t)
    (hth : 2 / (a * η₀) ≤ natCubeRoot (t + 1)) :
    stepSize η₀ t - stepSize η₀ (t + 1) ≤ a / 2 * stepSize η₀ (t + 1) * stepSize η₀ t := by
  have hp1 := stepSize_pos h0 ht
  have hp2 := stepSize_pos h0 (Nat.le_add_left 1 t)
  have hd := invStepSize_succ_sub_le h0 t
  rw [invStepSize_eq_inv h0 ht, invStepSize_eq_inv h0 (Nat.le_add_left 1 t)] at hd
  have hu := natCubeRoot_pos (Nat.le_add_left 1 t)
  have hle : 1 / (η₀ * natCubeRoot (t + 1)) ≤ a / 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hth
    nlinarith
  have key : (stepSize η₀ (t + 1))⁻¹ - (stepSize η₀ t)⁻¹ ≤ a / 2 := hd.trans hle
  have hprod : 0 < stepSize η₀ (t + 1) * stepSize η₀ t := mul_pos hp2 hp1
  have e : stepSize η₀ t - stepSize η₀ (t + 1) =
      ((stepSize η₀ (t + 1))⁻¹ - (stepSize η₀ t)⁻¹) * (stepSize η₀ (t + 1) * stepSize η₀ t) := by
    field_simp
  rw [e]
  nlinarith

/-- `(1/η_{t+1} − 1/η_t) √η_t ≤ η_t / (η₀ √η₀)` for `t ≥ 1`. -/
theorem invStepSize_succ_sub_mul_sqrt_le {η₀ : ℝ} (h0 : 0 < η₀) {t : ℕ} (ht : 1 ≤ t) :
    (invStepSize η₀ (t + 1) - invStepSize η₀ t) * √(stepSize η₀ t) ≤
      stepSize η₀ t / (η₀ * √η₀) := by
  have hu := natCubeRoot_pos ht
  have hu1 := natCubeRoot_pos (Nat.le_add_left 1 t)
  have hmono : natCubeRoot t ≤ natCubeRoot (t + 1) := natCubeRoot_mono (Nat.le_succ t)
  have hsq : √(stepSize η₀ t) = √η₀ / natCubeRoot t := by
    rw [stepSize_eq, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hu.le]
  have hs0 : 0 < √η₀ := Real.sqrt_pos.2 h0
  have hc : 0 ≤ invStepSize η₀ (t + 1) - invStepSize η₀ t :=
    sub_nonneg.2 (invStepSize_mono h0 (Nat.le_succ t))
  calc (invStepSize η₀ (t + 1) - invStepSize η₀ t) * √(stepSize η₀ t)
      ≤ 1 / (η₀ * natCubeRoot (t + 1)) * (√η₀ / natCubeRoot t) := by
        rw [hsq]; exact mul_le_mul_of_nonneg_right (invStepSize_succ_sub_le h0 t) (by positivity)
    _ ≤ 1 / (η₀ * natCubeRoot t) * (√η₀ / natCubeRoot t) := by
        gcongr
    _ = stepSize η₀ t / (η₀ * √η₀) := by
        rw [stepSize_eq]
        field_simp
        rw [Real.sq_sqrt h0.le]

/-- `(1/η_T) √η_T = T^{1/3} / √η₀` for `T ≥ 1`. -/
theorem invStepSize_mul_sqrt_eq {η₀ : ℝ} (h0 : 0 < η₀) {t : ℕ} (ht : 1 ≤ t) :
    invStepSize η₀ t * √(stepSize η₀ t) = natCubeRoot t / √η₀ := by
  have hu := natCubeRoot_pos ht
  have hs0 : 0 < √η₀ := Real.sqrt_pos.2 h0
  rw [invStepSize, stepSize_eq, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hu.le]
  field_simp
  rw [Real.sq_sqrt h0.le]

end StatisticalRL.Ch7Rest.TDInference
