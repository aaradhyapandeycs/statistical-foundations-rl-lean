import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Cube roots of natural numbers and a step-size recursion

Generic real-analysis facts for stochastic-approximation schedules `η_t = η₀ t^{-2/3}`, reduced to the
cube root `u_t = t^{1/3}` (`natCubeRoot`), for which `u_{t+1}³ − u_t³ = 1`. Mathlib-only imports;
intended to sit beside `Formalization/Analysis/StepSizeSums.lean` (same namespace, no name clashes).

* `sq_sub_sq_le_inv_of_cube_sub_eq_one`, `inv_sq_le_three_mul_sub_of_cube_sub_eq_one`: for
  `a ≥ b` (resp. `a ≥ b ≥ 0`), `a > 0`, `a³ − b³ = 1`: `a² − b² ≤ 1/a` and `1/a² ≤ 3(a − b)`.
* `natCubeRoot` API: `_nonneg`, `_pos`, `_cube`, `_mono`, `_succ_cube_sub`, `_one`,
  `natCast_rpow_two_thirds_eq` (`t^{2/3} = u_t²`), `natCubeRoot_div_sqrt_eq` (`u_T/√T = T^{-1/6}`).
* `sum_range_inv_sq_natCubeRoot_succ_le`: `∑_{t=1}^n t^{-2/3} ≤ 3 n^{1/3}`.
* `stepRecursion_le`: one step of the Chung-type induction
  `u ≤ C η_prev ⟹ (1 − aη)u + bη² ≤ Cη` when `2b ≤ aC` and `η_prev − η ≤ (a/2) η η_prev`.
-/

open Finset

namespace StatisticalRL.Probability

/-- `a² − b² ≤ 1/a` when `a ≥ b`, `a > 0` and `a³ − b³ = 1`. -/
theorem sq_sub_sq_le_inv_of_cube_sub_eq_one {a b : ℝ} (hab : b ≤ a) (ha : 0 < a)
    (h : a ^ 3 - b ^ 3 = 1) : a ^ 2 - b ^ 2 ≤ 1 / a := by
  rw [le_div_iff₀ ha]
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (sq_nonneg b)]

/-- `1/a² ≤ 3(a − b)` when `a ≥ b ≥ 0`, `a > 0` and `a³ − b³ = 1`. -/
theorem inv_sq_le_three_mul_sub_of_cube_sub_eq_one {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (ha : 0 < a) (h : a ^ 3 - b ^ 3 = 1) : 1 / a ^ 2 ≤ 3 * (a - b) := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (mul_nonneg hb (sub_nonneg.2 hab)),
    mul_nonneg (sub_nonneg.2 hab) (mul_nonneg (sub_nonneg.2 hab) (add_nonneg hb ha.le))]

/-- The cube root `u_t = t^{1/3}`. -/
noncomputable def natCubeRoot (t : ℕ) : ℝ := (t : ℝ) ^ (1 / 3 : ℝ)

theorem natCubeRoot_nonneg (t : ℕ) : 0 ≤ natCubeRoot t := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem natCubeRoot_pos {t : ℕ} (ht : 1 ≤ t) : 0 < natCubeRoot t :=
  Real.rpow_pos_of_pos (by exact_mod_cast ht) _

theorem natCubeRoot_cube (t : ℕ) : natCubeRoot t ^ 3 = t := by
  rw [natCubeRoot, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem natCubeRoot_mono {s t : ℕ} (h : s ≤ t) : natCubeRoot s ≤ natCubeRoot t :=
  Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by norm_num)

theorem natCubeRoot_succ_cube_sub (t : ℕ) : natCubeRoot (t + 1) ^ 3 - natCubeRoot t ^ 3 = 1 := by
  rw [natCubeRoot_cube, natCubeRoot_cube]; push_cast; ring

theorem natCast_rpow_two_thirds_eq (t : ℕ) : (t : ℝ) ^ (2 / 3 : ℝ) = natCubeRoot t ^ 2 := by
  rw [natCubeRoot, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem natCubeRoot_one : natCubeRoot 1 = 1 := by simp [natCubeRoot]

theorem natCubeRoot_div_sqrt_eq {T : ℕ} (hT : 1 ≤ T) :
    natCubeRoot T / Real.sqrt T = (T : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [natCubeRoot, Real.sqrt_eq_rpow, ← Real.rpow_sub hT0]
  norm_num

/-- `∑_{t=1}^n 1/u_t² ≤ 3 u_n`, i.e. `∑_{t=1}^n t^{-2/3} ≤ 3 n^{1/3}`. -/
theorem sum_range_inv_sq_natCubeRoot_succ_le (n : ℕ) :
    ∑ t ∈ range n, 1 / natCubeRoot (t + 1) ^ 2 ≤ 3 * natCubeRoot n := by
  have hterm : ∀ t ∈ range n, 1 / natCubeRoot (t + 1) ^ 2 ≤
      3 * (natCubeRoot (t + 1) - natCubeRoot t) := fun t _ ↦
    inv_sq_le_three_mul_sub_of_cube_sub_eq_one (natCubeRoot_nonneg t)
      (natCubeRoot_mono (Nat.le_succ t)) (natCubeRoot_pos (Nat.le_add_left 1 t))
      (natCubeRoot_succ_cube_sub t)
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← mul_sum, sum_range_sub (fun t ↦ natCubeRoot t)]
  simp [natCubeRoot]

/-- One step of the Chung-type induction for `u_t ≤ (1 − aη_t) u_{t−1} + b η_t²`:
if `u ≤ C η_prev`, `2b ≤ aC`, `aη ≤ 1`, `η ≤ η_prev`, and the schedule varies slowly,
`η_prev − η ≤ (a/2) η η_prev`, then `(1 − aη) u + b η² ≤ C η`. -/
theorem stepRecursion_le {a b C η ηprev u : ℝ} (hη : 0 ≤ η) (haη : a * η ≤ 1) (hC : 0 ≤ C)
    (hbC : 2 * b ≤ a * C) (hηle : η ≤ ηprev)
    (hslow : ηprev - η ≤ a / 2 * η * ηprev) (hu : u ≤ C * ηprev) :
    (1 - a * η) * u + b * η ^ 2 ≤ C * η := by
  have h1 : (1 - a * η) * u ≤ (1 - a * η) * (C * ηprev) :=
    mul_le_mul_of_nonneg_left hu (by linarith)
  have h2 : C * (ηprev - η) ≤ C * (a / 2 * η * ηprev) := mul_le_mul_of_nonneg_left hslow hC
  have h3 : b * η ^ 2 ≤ a * C / 2 * η * ηprev := by
    have hη2 : η ^ 2 ≤ η * ηprev := by rw [sq]; exact mul_le_mul_of_nonneg_left hηle hη
    have hb' : b * η ^ 2 ≤ b * (η * ηprev) ∨ b < 0 := by
      rcases le_or_gt 0 b with hb | hb
      · exact Or.inl (mul_le_mul_of_nonneg_left hη2 hb)
      · exact Or.inr hb
    have hηη : 0 ≤ η * ηprev := mul_nonneg hη (hη.trans hηle)
    rcases hb' with hb' | hb'
    · nlinarith
    · nlinarith [sq_nonneg η]
  nlinarith

end StatisticalRL.Probability
