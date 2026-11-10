import Formalization.RobustRL.LowerBounds.TrapCore

/-!
# The printed Theorems 7.2 and 7.4 are false (SOURCE-ISSUES C37)

For every pair of constants and every rounding of `T = C₁ log(N/(1-γ))` within
distance `< 1`, the horizon trap with

* `k ∈ ℕ` large (depending only on the constants), `γ = 1 - 1/k²`,
  `σ = (1/k²)² = (1-γ)²`, `δ = 1/2`, `ε = 1`, `N = k¹⁰`,
* `L = ⌈C₁ log(N/(1-γ))⌉₊ = ⌈12 C₁ log k⌉₊`, `S = L+3`, `A = 2`

satisfies every printed hypothesis (γ ≥ 1/4, the σ-, δ- and ε-ranges, and the
printed sample-size condition), while the printed success event has
probability `0 < 1 - δ`: DRVI (from `Q̂₀ = 0`) bails at `s₀` for every greedy
selector and the true robust gap at `s₀` exceeds `3/2 > ε`.

* 7.2 (TV, `σ ∈ (0,1)`): `not_thm7_2_printed`.
* 7.4 (χ², `σ ∈ (0,∞)`): `not_thm7_4_printed`.
-/

open MeasureTheory

namespace StatisticalRL.RobustRL.Ch7.HorizonTrap

open StatisticalRL.EnvironmentStage

local instance horizonTrapStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-! ## Arithmetic -/

theorem choose_k (C₁ K : ℝ) : ∃ k : ℕ, 3 ≤ (k : ℝ) ∧ 48 * C₁ + 8 ≤ (k : ℝ) ∧
    2 * K * (48 * C₁ + 28) ≤ (k : ℝ) ∧ Real.exp (1 / (12 * C₁)) ≤ (k : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge
    (max (max 3 (48 * C₁ + 8)) (max (2 * K * (48 * C₁ + 28)) (Real.exp (1 / (12 * C₁)))))
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans hk)

theorem log_bound {kr C₁ : ℝ} {L m : ℕ} (hk : 1 ≤ kr)
    (hL : (L : ℝ) ≤ 12 * C₁ * kr + 1) (hm : m ≤ 12) :
    Real.log (4 * ((L : ℝ) + 3) * kr ^ m) ≤ kr * (48 * C₁ + 28) := by
  have hkpos : 0 < kr := by linarith
  have hA : (0 : ℝ) < 4 * ((L : ℝ) + 3) := by positivity
  rw [Real.log_mul hA.ne' (pow_pos hkpos m).ne', Real.log_pow]
  have h1 := Real.log_le_sub_one_of_pos hA
  have h2 := Real.log_le_sub_one_of_pos hkpos
  have h3 : 0 ≤ Real.log kr := Real.log_nonneg hk
  have hm' : (m : ℝ) ≤ 12 := by exact_mod_cast hm
  have h4 : (m : ℝ) * Real.log kr ≤ 12 * kr := by
    calc (m : ℝ) * Real.log kr ≤ 12 * Real.log kr :=
          mul_le_mul_of_nonneg_right hm' h3
      _ ≤ 12 * kr := by linarith
  nlinarith

theorem trap_gap_bound {u : ℝ} {L : ℕ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 9)
    (hL : 4 * ((L : ℝ) + 1) * u ≤ 1) :
    1 < ((1 - u) * (1 - u ^ 2)) ^ (L + 1) / (1 - (1 - u) * (1 - u ^ 2)) - 1 / 2 := by
  set q := (1 - u) * (1 - u ^ 2) with hq
  have hw : 1 - q = u + u ^ 2 - u ^ 3 := by rw [hq]; ring
  have hwpos : 0 < 1 - q := by
    rw [hw]
    have : u ^ 3 ≤ u ^ 2 := by nlinarith
    nlinarith
  have hwle : 1 - q ≤ 2 * u := by
    rw [hw]
    have : u ^ 2 ≤ u := by nlinarith
    nlinarith
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ q - 1 by nlinarith) (L + 1)
  rw [show 1 + (q - 1) = q by ring] at hbern
  push_cast at hbern
  have hhalf : 1 / 2 ≤ q ^ (L + 1) := by
    have : ((L : ℝ) + 1) * (1 - q) ≤ 1 / 2 := by
      calc ((L : ℝ) + 1) * (1 - q) ≤ ((L : ℝ) + 1) * (2 * u) :=
            mul_le_mul_of_nonneg_left hwle (by positivity)
        _ ≤ 1 / 2 := by linarith
    nlinarith
  have : 3 / 2 < q ^ (L + 1) / (1 - q) := by
    rw [lt_div_iff₀ hwpos]
    nlinarith
  linarith

/-! ## Trap parameters -/

/-- The common parameter package for a natural `k ≥ 3` and a constant `C₁`. -/
structure Params (C₁ : ℝ) (k : ℕ) : Prop where
  hk3 : 3 ≤ (k : ℝ)
  hkC : 48 * C₁ + 8 ≤ (k : ℝ)
  hkE : Real.exp (1 / (12 * C₁)) ≤ (k : ℝ)

section Params

variable {C₁ : ℝ} {k : ℕ}

/-- `γ = 1 - 1/k²`. -/
noncomputable def gam (k : ℕ) : ℝ := 1 - 1 / (k : ℝ) ^ 2

/-- The real number `C₁ log(N/(1-γ))` at `N = k¹⁰`, `γ = 1 - 1/k²`. -/
noncomputable def yval (C₁ : ℝ) (k : ℕ) : ℝ :=
  C₁ * Real.log (((k ^ 10 : ℕ) : ℝ) / (1 - gam k))

/-- Chain length `L = ⌈C₁ log(N/(1-γ))⌉₊`. -/
noncomputable def chainLen (C₁ : ℝ) (k : ℕ) : ℕ := ⌈yval C₁ k⌉₊

theorem kr_pos (hp : Params C₁ k) : (0 : ℝ) < k := by linarith [hp.hk3]

theorem one_sub_gam (k : ℕ) : 1 - gam k = 1 / (k : ℝ) ^ 2 := by unfold gam; ring

theorem u_pos (hp : Params C₁ k) : 0 < 1 / (k : ℝ) ^ 2 := by
  have := kr_pos hp; positivity

theorem u_le (hp : Params C₁ k) : 1 / (k : ℝ) ^ 2 ≤ 1 / 9 := by
  have h3 := hp.hk3
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem gam_nonneg (hp : Params C₁ k) : 0 ≤ gam k := by
  have := u_le hp; unfold gam; linarith

theorem gam_lt_one (hp : Params C₁ k) : gam k < 1 := by
  have := u_pos hp; unfold gam; linarith

theorem gam_ge_quarter (hp : Params C₁ k) : 1 / 4 ≤ gam k := by
  have := u_le hp; unfold gam; linarith

theorem yval_eq (hp : Params C₁ k) : yval C₁ k = 12 * C₁ * Real.log k := by
  have hk := kr_pos hp
  unfold yval
  rw [one_sub_gam]
  have : ((k ^ 10 : ℕ) : ℝ) / (1 / (k : ℝ) ^ 2) = (k : ℝ) ^ 12 := by
    push_cast; field_simp
  rw [this, Real.log_pow]
  push_cast; ring

theorem yval_ge_one (hC₁ : 0 < C₁) (hp : Params C₁ k) : 1 ≤ yval C₁ k := by
  rw [yval_eq hp]
  have hlog : 1 / (12 * C₁) ≤ Real.log k :=
    (Real.le_log_iff_exp_le (kr_pos hp)).2 hp.hkE
  rw [div_le_iff₀ (by positivity)] at hlog
  linarith

theorem yval_le (hC₁ : 0 < C₁) (hp : Params C₁ k) : yval C₁ k ≤ 12 * C₁ * k := by
  rw [yval_eq hp]
  have := Real.log_le_sub_one_of_pos (kr_pos hp)
  have : 12 * C₁ * Real.log k ≤ 12 * C₁ * (k - 1) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  linarith

theorem chainLen_le (hC₁ : 0 < C₁) (hp : Params C₁ k) :
    (chainLen C₁ k : ℝ) ≤ 12 * C₁ * k + 1 := by
  have h0 : 0 ≤ yval C₁ k := le_trans zero_le_one (yval_ge_one hC₁ hp)
  have := Nat.ceil_lt_add_one h0
  have := yval_le hC₁ hp
  unfold chainLen; linarith

theorem rounded_bounds (hC₁ : 0 < C₁) (hp : Params C₁ k) {roundT : ℝ → ℕ}
    (hround : RoundsReal roundT) :
    1 ≤ roundT (yval C₁ k) ∧ roundT (yval C₁ k) ≤ chainLen C₁ k + 1 := by
  have hy1 := yval_ge_one hC₁ hp
  have h := abs_lt.1 (hround (yval C₁ k) (by linarith))
  have hceil : yval C₁ k ≤ (chainLen C₁ k : ℝ) := Nat.le_ceil _
  constructor
  · have : (0 : ℝ) < roundT (yval C₁ k) := by linarith [h.1]
    exact_mod_cast this
  · have : (roundT (yval C₁ k) : ℝ) < (chainLen C₁ k : ℝ) + 1 := by linarith [h.2]
    have : roundT (yval C₁ k) < chainLen C₁ k + 1 := by exact_mod_cast this
    omega

theorem gap_gt (hC₁ : 0 < C₁) (hp : Params C₁ k) :
    1 < (gam k * (1 - (1 / (k : ℝ) ^ 2) ^ 2)) ^ (chainLen C₁ k + 1) /
      (1 - gam k * (1 - (1 / (k : ℝ) ^ 2) ^ 2)) - 1 / 2 := by
  have hk := kr_pos hp
  have hL := chainLen_le hC₁ hp
  have hcond : 4 * ((chainLen C₁ k : ℝ) + 1) * (1 / (k : ℝ) ^ 2) ≤ 1 := by
    rw [← mul_div_assoc, mul_one, div_le_one (by positivity)]
    have := hp.hkC
    nlinarith
  have := trap_gap_bound (u_pos hp) (u_le hp) hcond
  unfold gam
  exact this

theorem log_arg_bound (hC₁ : 0 < C₁) (hp : Params C₁ k) {m : ℕ} (hm : m ≤ 12) :
    Real.log (4 * ((chainLen C₁ k : ℝ) + 3) * (k : ℝ) ^ m) ≤ (k : ℝ) * (48 * C₁ + 28) :=
  log_bound (by linarith [hp.hk3]) (chainLen_le hC₁ hp) hm

end Params

/-! ## Assembly -/

/-- With the trap parameters, the printed success event has `.real` measure `0`. -/
theorem trap_success_real_zero {C₁ : ℝ} {k : ℕ} (ball : RowBall (Fin (chainLen C₁ k + 3)))
    (hC₁ : 0 < C₁) (hp : Params C₁ k) (hball : TrapBall ball ((1 / (k : ℝ) ^ 2) ^ 2))
    {roundT : ℝ → ℕ} (hround : RoundsReal roundT) (hN : 0 < k ^ 10)
    (pick : ModelBasedPolicyLearning.Samples (Fin (chainLen C₁ k + 3)) (Fin 2) (k ^ 10) →
      Fin (chainLen C₁ k + 3) → Fin 2)
    (hpick : ∀ data, IsGreedy (empiricalDRVI ball
      (trapMDP (chainLen C₁ k) (gam k) (gam_nonneg hp) (gam_lt_one hp))
      ((1 / (k : ℝ) ^ 2) ^ 2) (k ^ 10) hN data (roundT (yval C₁ k))) (pick data)) :
    (ModelBasedPolicyLearning.samplingLaw
        (trapMDP (chainLen C₁ k) (gam k) (gam_nonneg hp) (gam_lt_one hp)) (k ^ 10)).real
      {data | ∀ s, robustOptimalValue ball
          (trapMDP (chainLen C₁ k) (gam k) (gam_nonneg hp) (gam_lt_one hp))
          ((1 / (k : ℝ) ^ 2) ^ 2) s -
        robustPolicyValue ball
          (trapMDP (chainLen C₁ k) (gam k) (gam_nonneg hp) (gam_lt_one hp))
          ((1 / (k : ℝ) ^ 2) ^ 2) (detPolicy (pick data)) s ≤ 1} = 0 := by
  have hu := u_pos hp
  have hu9 := u_le hp
  have hσ0 : 0 ≤ (1 / (k : ℝ) ^ 2) ^ 2 := by positivity
  have hσ1 : (1 / (k : ℝ) ^ 2) ^ 2 ≤ 1 := by nlinarith
  obtain ⟨hT1, hTL⟩ := rounded_bounds hC₁ hp hround
  have h0 := trap_success_null ball hσ0 hσ1 hball (k ^ 10) hN (roundT (yval C₁ k)) hT1 hTL 1
    (gap_gt hC₁ hp) pick hpick
  rw [Measure.real, h0]
  rfl

/-- **C37 (Theorem 7.2), existential tie-rule reading.** For every rounding of
`T` within distance `< 1` (floor, ceiling, nearest), no choice of constants makes
even *some* greedy DRVI selector satisfy the printed clause. -/
theorem not_thm7_2_printed_exists_tie (roundT : ℝ → ℕ) (hround : RoundsReal roundT) :
    ¬ Thm7_2_printed_existsTie roundT := by
  rintro ⟨C₁, C₂, hC₁, hC₂, h⟩
  obtain ⟨k, hk3, hkC, hkK, hkE⟩ := choose_k C₁ C₂
  have hp : Params C₁ k := ⟨hk3, hkC, hkE⟩
  have hk := kr_pos hp
  have hu := u_pos hp
  have hu9 := u_le hp
  set L := chainLen C₁ k
  set u : ℝ := 1 / (k : ℝ) ^ 2 with hudef
  have hN : 0 < k ^ 10 := by
    have : 0 < k := by exact_mod_cast hk
    positivity
  have hmax : max (1 - gam k) (u ^ 2) = u := by
    rw [one_sub_gam, max_eq_left]; nlinarith
  have hmain := h (Fin (L + 3)) (Fin 2) (trapMDP L (gam k) (gam_nonneg hp) (gam_lt_one hp))
    (u ^ 2) (1 / 2) 1 (k ^ 10) hN (gam_ge_quarter hp) (by positivity) (by nlinarith)
    (by norm_num) (by norm_num) one_pos ?_ ?_
  · obtain ⟨pick, hpick, hmain⟩ := hmain
    rw [trap_success_real_zero tvBall hC₁ hp (tvBall_trapBall (by positivity)) hround hN pick
      hpick] at hmain
    norm_num at hmain
  · -- ε = 1 ≤ √(1/max(1-γ,σ))
    change (1 : ℝ) ≤ Real.sqrt (1 / max (1 - gam k) (u ^ 2))
    rw [hmax]
    have h1 : (1 : ℝ) ≤ 1 / u := by rw [le_div_iff₀ hu]; linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 / u) := Real.sqrt_le_sqrt h1
  · -- the printed sample-size condition
    change C₂ / ((1 - gam k) ^ 2 * max (1 - gam k) (u ^ 2) * 1 ^ 2) *
        Real.log (Fintype.card (Fin (L + 3)) * Fintype.card (Fin 2) * ((k ^ 10 : ℕ) : ℝ) /
          ((1 - gam k) * (1 / 2))) ≤ ((k ^ 10 : ℕ) : ℝ)
    rw [hmax, one_sub_gam, ← hudef, Fintype.card_fin, Fintype.card_fin]
    have harg : ((L + 3 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * ((k ^ 10 : ℕ) : ℝ) / (u * (1 / 2)) =
        4 * ((L : ℝ) + 3) * (k : ℝ) ^ 12 := by
      rw [hudef]; push_cast; field_simp; ring
    rw [harg]
    have hlog := log_arg_bound hC₁ hp (m := 12) le_rfl
    have hpre : C₂ / (u ^ 2 * u * 1 ^ 2) = C₂ * (k : ℝ) ^ 6 := by
      rw [hudef]; field_simp
    rw [hpre]
    push_cast
    calc C₂ * (k : ℝ) ^ 6 * Real.log (4 * ((L : ℝ) + 3) * (k : ℝ) ^ 12)
        ≤ C₂ * (k : ℝ) ^ 6 * ((k : ℝ) * (48 * C₁ + 28)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (k : ℝ) ^ 7 * (C₂ * (48 * C₁ + 28)) := by ring
      _ ≤ (k : ℝ) ^ 7 * (k : ℝ) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (k : ℝ) ≤ (k : ℝ) ^ 3 := by nlinarith
          nlinarith
      _ = (k : ℝ) ^ 10 := by ring

/-- **C37 (Theorem 7.4), existential tie-rule reading.** For every rounding of
`T` within distance `< 1`, no choice of constants makes even *some* greedy DRVI
selector satisfy the printed clause. -/
theorem not_thm7_4_printed_exists_tie (roundT : ℝ → ℕ) (hround : RoundsReal roundT) :
    ¬ Thm7_4_printed_existsTie roundT := by
  rintro ⟨c₁, c₂, hc₁, hc₂, h⟩
  obtain ⟨k, hk3, hkC, hkK, hkE⟩ := choose_k c₁ c₂
  have hp : Params c₁ k := ⟨hk3, hkC, hkE⟩
  have hk := kr_pos hp
  have hu := u_pos hp
  have hu9 := u_le hp
  set L := chainLen c₁ k
  set u : ℝ := 1 / (k : ℝ) ^ 2 with hudef
  have hN : 0 < k ^ 10 := by
    have : 0 < k := by exact_mod_cast hk
    positivity
  have hmain := h (Fin (L + 3)) (Fin 2) (trapMDP L (gam k) (gam_nonneg hp) (gam_lt_one hp))
    (u ^ 2) (1 / 2) 1 (k ^ 10) hN (by positivity) (gam_ge_quarter hp)
    (by norm_num) (by norm_num) one_pos ?_ ?_
  · obtain ⟨pick, hpick, hmain⟩ := hmain
    rw [trap_success_real_zero chiBall hc₁ hp (chiBall_trapBall (by positivity)) hround hN pick
      hpick] at hmain
    norm_num at hmain
  · -- ε = 1 ≤ 1/(1-γ)
    change (1 : ℝ) ≤ 1 / (1 - gam k)
    rw [one_sub_gam, ← hudef, le_div_iff₀ hu]; linarith
  · -- the printed sample-size condition
    change c₂ / ((1 - gam k) ^ 3 * 1 ^ 2) * (1 + max (Real.sqrt (u ^ 2)) (u ^ 2) / (1 - gam k)) *
        Real.log (Fintype.card (Fin (L + 3)) * Fintype.card (Fin 2) * ((k ^ 10 : ℕ) : ℝ) /
          (1 / 2)) ≤ ((k ^ 10 : ℕ) : ℝ)
    rw [one_sub_gam, ← hudef, Fintype.card_fin, Fintype.card_fin,
      Real.sqrt_sq hu.le, max_eq_left (by nlinarith), div_self hu.ne']
    have harg : ((L + 3 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * ((k ^ 10 : ℕ) : ℝ) / (1 / 2) =
        4 * ((L : ℝ) + 3) * (k : ℝ) ^ 10 := by
      push_cast; field_simp; ring
    rw [harg]
    have hlog := log_arg_bound hc₁ hp (m := 10) (by norm_num)
    have hpre : c₂ / (u ^ 3 * 1 ^ 2) * (1 + 1) = 2 * c₂ * (k : ℝ) ^ 6 := by
      rw [hudef]; field_simp; ring
    rw [hpre]
    push_cast
    calc 2 * c₂ * (k : ℝ) ^ 6 * Real.log (4 * ((L : ℝ) + 3) * (k : ℝ) ^ 10)
        ≤ 2 * c₂ * (k : ℝ) ^ 6 * ((k : ℝ) * (48 * c₁ + 28)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (k : ℝ) ^ 7 * (2 * c₂ * (48 * c₁ + 28)) := by ring
      _ ≤ (k : ℝ) ^ 7 * (k : ℝ) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (k : ℝ) ≤ (k : ℝ) ^ 3 := by nlinarith
          nlinarith
      _ = (k : ℝ) ^ 10 := by ring

/-- A greedy selector exists for any finite nonempty action set. -/
theorem exists_greedy_of_nonempty {State Action : Type*} [Finite Action] [Nonempty Action]
    (Q : State → Action → ℝ) : ∃ f, IsGreedy Q f := by
  choose f hf using fun s ↦ Finite.exists_max (Q s)
  exact ⟨f, fun s a ↦ hf s a⟩

/-- The every-tie-rule reading implies the existential one. -/
theorem thm7_2_printed_existsTie_of {roundT : ℝ → ℕ} (h : Thm7_2_printed roundT) :
    Thm7_2_printed_existsTie roundT := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := h
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro State Action _ _ M σ δ ε N hN h1 h2 h3 h4 h5 h6 h7 h8
  letI : Nonempty Action := M.action_nonempty
  choose pick hpick using fun data ↦ exists_greedy_of_nonempty (empiricalDRVI tvBall M σ N hN
    data (roundT (C₁ * Real.log (N / (1 - M.discount)))))
  exact ⟨pick, hpick, h State Action M σ δ ε N hN h1 h2 h3 h4 h5 h6 h7 h8 pick hpick⟩

/-- The every-tie-rule reading implies the existential one. -/
theorem thm7_4_printed_existsTie_of {roundT : ℝ → ℕ} (h : Thm7_4_printed roundT) :
    Thm7_4_printed_existsTie roundT := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := h
  refine ⟨c₁, c₂, hc₁, hc₂, ?_⟩
  intro State Action _ _ M σ δ ε N hN h1 h2 h3 h4 h5 h6 h7
  letI : Nonempty Action := M.action_nonempty
  choose pick hpick using fun data ↦ exists_greedy_of_nonempty (empiricalDRVI chiBall M σ N hN
    data (roundT (c₁ * Real.log (N / (1 - M.discount)))))
  exact ⟨pick, hpick, h State Action M σ δ ε N hN h1 h2 h3 h4 h5 h6 h7 pick hpick⟩

/-- **C37 (Theorem 7.2).** For every rounding of `T` within distance `< 1`
(floor, ceiling, nearest), the printed Theorem 7.2 (every tie rule) is false.

Scope: this refutes only the printed iteration count `T = C₁ log(N/(1-γ))`,
using an extreme-regime witness (`γ = 1 - 1/k²` with `k` large in terms of the
constants, `σ = (1-γ)²`, `N = k¹⁰`, `S = ⌈12 C₁ log k⌉₊ + 3`). It says nothing
about a corrected statement with `T ≳ log(N/(1-γ))/(1-γ)`, nor about the
statistical rate; neither is proved here. -/
theorem not_thm7_2_printed (roundT : ℝ → ℕ) (hround : RoundsReal roundT) :
    ¬ Thm7_2_printed roundT := fun h ↦
  not_thm7_2_printed_exists_tie roundT hround (thm7_2_printed_existsTie_of h)

/-- **C37 (Theorem 7.4).** For every rounding of `T` within distance `< 1`,
the printed Theorem 7.4 (every tie rule) is false. Same scope as
`not_thm7_2_printed`: only the printed iteration count is refuted, with an
extreme-regime witness; the corrected iteration count is untouched. -/
theorem not_thm7_4_printed (roundT : ℝ → ℕ) (hround : RoundsReal roundT) :
    ¬ Thm7_4_printed roundT := fun h ↦
  not_thm7_4_printed_exists_tie roundT hround (thm7_4_printed_existsTie_of h)

/-- The floor rounding is admissible. -/
theorem roundsReal_floor : RoundsReal (fun y ↦ ⌊y⌋₊) := by
  intro y hy
  rw [abs_lt]
  constructor
  · linarith [Nat.lt_floor_add_one y]
  · linarith [Nat.floor_le hy]

/-- The ceiling rounding is admissible. -/
theorem roundsReal_ceil : RoundsReal (fun y ↦ ⌈y⌉₊) := by
  intro y hy
  rw [abs_lt]
  constructor
  · linarith [Nat.le_ceil y]
  · linarith [Nat.ceil_lt_add_one hy]

theorem not_thm7_2_printed_ceil : ¬ Thm7_2_printed (fun y ↦ ⌈y⌉₊) :=
  not_thm7_2_printed _ roundsReal_ceil

theorem not_thm7_4_printed_ceil : ¬ Thm7_4_printed (fun y ↦ ⌈y⌉₊) :=
  not_thm7_4_printed _ roundsReal_ceil

theorem not_thm7_2_printed_floor : ¬ Thm7_2_printed (fun y ↦ ⌊y⌋₊) :=
  not_thm7_2_printed _ roundsReal_floor

theorem not_thm7_4_printed_floor : ¬ Thm7_4_printed (fun y ↦ ⌊y⌋₊) :=
  not_thm7_4_printed _ roundsReal_floor

end StatisticalRL.RobustRL.Ch7.HorizonTrap
