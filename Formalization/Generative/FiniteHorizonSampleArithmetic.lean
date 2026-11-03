import Formalization.Generative.FiniteHorizonPolicyPerformanceConsumption

/-! Explicit conservative logarithm and sample-threshold arithmetic.
No new probabilistic estimate or policy-selection assumption occurs. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem allLevelBeta_eq_log {H : ℕ} (δ : ℝ) :
    allLevelBeta (H := H) State Action δ =
      2 * Real.log (8 * (Nat.log 2 H + 1) * Fintype.card (Fin H × State × Action) / δ) := by
  unfold allLevelBeta allLevelConfidence
  congr 2
  rw [div_div_eq_mul_div]
  ring

/-- K counts levels, not policies or future-data codes. -/
theorem auxiliary_levelCount_le_horizon (H : ℕ) (hH : 0 < H) : Nat.log 2 H + 1 ≤ H := by
  exact Nat.succ_le_of_lt (Nat.log_lt_self 2 hH.ne')

/-- A safe log absorption valid already for T≥2; no singleton-state branch. -/
theorem auxiliary_safe_log_bound (T K δ : ℝ) (hT : 2 ≤ T) (hK : 1 ≤ K)
    (hKT : K ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) :
    2 * Real.log (8 * K * T / δ) ≤ 10 * Real.log (T / δ) := by
  have hTp : 0 < T := by linarith
  have hKp : 0 < K := by linarith
  have hlogK : Real.log K ≤ Real.log T := Real.log_le_log hKp hKT
  have hlog2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 3
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 3 = 8 by norm_num] at hh
    exact hh
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1.le
  rw [Real.log_div (by positivity) hδ.ne', Real.log_mul (by positivity) hTp.ne',
    Real.log_mul (by norm_num) hKp.ne', hlog8, Real.log_div hTp.ne' hδ.ne']
  linarith

theorem allLevelBeta_le_source_log {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (hH : 2 ≤ H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    allLevelBeta (H := H) State Action δ ≤
      10 * Real.log ((Fintype.card (Fin H × State × Action) : ℝ) / δ) := by
  have hHp : 0 < H := by omega
  letI : Nonempty State := (E ⟨0,hHp⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hHp⟩).action_nonempty
  have hs : 1 ≤ Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have ha : 1 ≤ Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  have hSA : 1 ≤ Fintype.card State * Fintype.card Action := by nlinarith
  have hrow : H ≤ Fintype.card (Fin H × State × Action) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, mul_one] using Nat.mul_le_mul_left H hSA
  rw [allLevelBeta_eq_log]
  apply auxiliary_safe_log_bound
  · exact_mod_cast hH.trans hrow
  · have hh : 1 ≤ Nat.log 2 H + 1 := by omega
    exact_mod_cast hh
  · have hh := (auxiliary_levelCount_le_horizon H hHp).trans hrow
    exact_mod_cast hh
  · exact hδ
  · exact hδ1

/-- The final numerical threshold supplies both strict contraction and ε error.
The constant 8640 retains a factor two of slack after β≤10log(T/δ). -/
theorem auxiliary_sample_threshold_arithmetic (H N ε β L : ℝ)
    (hH : 0 < H) (hN : 0 < N) (hε : 0 < ε) (hεH : ε ≤ H)
    (hβ : 0 < β) (hβL : β ≤ 10 * L)
    (hsize : 8640 * H ^ 3 * L / ε ^ 2 ≤ N) :
    12 * H * β < N ∧ 12 * H * Real.sqrt (3 * β * H / N) ≤ ε := by
  have hH0 := hH.le
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hβH : 0 < H * β := mul_pos hH hβ
  have heH : ε ^ 2 ≤ H ^ 2 := (sq_le_sq₀ hε.le hH.le).2 hεH
  have hmain : 8640 * H ^ 3 * L ≤ N * ε ^ 2 := (div_le_iff₀ hε2).mp hsize
  have hβprod := mul_le_mul_of_nonneg_left hβL (by positivity : 0 ≤ 864 * H ^ 3)
  have hmid : 864 * H ^ 3 * β ≤ N * ε ^ 2 := by nlinarith
  have hNh := mul_le_mul_of_nonneg_left heH hN.le
  have hcancel : 864 * H * β ≤ N := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hH)).mp
    nlinarith
  have hs : 12 * H * β < N := by nlinarith
  have harg : 0 ≤ 3 * β * H / N := by positivity
  have hroot := Real.sq_sqrt harg
  have he : (12 * H * Real.sqrt (3 * β * H / N)) ^ 2 = 432 * H ^ 3 * β / N := by
    rw [mul_pow, mul_pow, hroot]
    ring
  have herrsq : (12 * H * Real.sqrt (3 * β * H / N)) ^ 2 ≤ ε ^ 2 := by
    rw [he]
    apply (div_le_iff₀ hN).2
    nlinarith
  exact ⟨hs, by nlinarith [Real.sqrt_nonneg (3 * β * H / N)]⟩

theorem allLevelBeta_pos {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < allLevelBeta (H := H) State Action δ := by
  have he := allLevelConfidence_bounds E hH δ hδ hδ1
  exact mul_pos (by norm_num) (Real.log_pos ((lt_div_iff₀ he.1).2 (by linarith)))

end StatisticalRL.FiniteHorizonGenerative
