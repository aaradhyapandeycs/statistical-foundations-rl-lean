import Formalization.Generative.PolicyLearningAbsorbingLipschitz
import Mathlib.Algebra.Order.Floor.Ring

/-! The source finite parameter grid, its actual absorbing value family,
covering property and Bernstein-logarithm count. No independence is asserted
for the data-selected covering index. -/
open scoped BigOperators
namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance gridRealDecidable : DecidableEq ℝ := Classical.decEq ℝ
noncomputable local instance gridValueDecidable : DecidableEq (State → ℝ) := Classical.decEq _

noncomputable def absorbingGridStep (M : DiscountedMDP State Action) (N : ℕ) (_hN : 0 < N) : ℝ :=
  1 / ((N : ℝ) * (1 - M.discount))

noncomputable def absorbingGridPoint (M : DiscountedMDP State Action) (N : ℕ) (_hN : 0 < N)
    (i : Fin (N + 1)) : ℝ := (i : ℝ) / ((N : ℝ) * (1 - M.discount))

noncomputable def absorbingParameterGrid (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    Finset ℝ := Finset.univ.image (absorbingGridPoint M N hN)

theorem absorbingGridStep_pos (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    0 < absorbingGridStep M N hN := by
  unfold absorbingGridStep
  exact one_div_pos.mpr (mul_pos (by exact_mod_cast hN) (sub_pos.mpr M.discount_lt_one))

theorem absorbingGridPoint_bounds (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (i : Fin (N + 1)) :
    0 ≤ absorbingGridPoint M N hN i ∧ absorbingGridPoint M N hN i ≤ 1 / (1 - M.discount) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hi : (i : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  constructor
  · exact div_nonneg (by positivity) (mul_pos hn hh).le
  · unfold absorbingGridPoint
    apply (div_le_iff₀ (mul_pos hn hh)).2
    have heq : 1 / (1 - M.discount) * ((N : ℝ) * (1 - M.discount)) = N := by
      field_simp
    rw [heq]
    exact hi

theorem absorbingGridPoint_zero (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    absorbingGridPoint M N hN ⟨0, by omega⟩ = 0 := by simp [absorbingGridPoint]

theorem absorbingGridPoint_last (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    absorbingGridPoint M N hN ⟨N, Nat.lt_succ_self N⟩ = 1 / (1 - M.discount) := by
  unfold absorbingGridPoint
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp

theorem absorbingGridPoint_injective (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    Function.Injective (absorbingGridPoint M N hN) := by
  intro i j hij
  have hd : (N : ℝ) * (1 - M.discount) ≠ 0 :=
    ne_of_gt (mul_pos (by exact_mod_cast hN) (sub_pos.mpr M.discount_lt_one))
  have he : (i : ℝ) = (j : ℝ) := (div_left_inj' hd).mp hij
  apply Fin.ext
  exact_mod_cast he

theorem absorbingParameterGrid_card (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    (absorbingParameterGrid M N hN).card = N + 1 := by
  rw [absorbingParameterGrid, Finset.card_image_of_injective _ (absorbingGridPoint_injective M N hN)]
  simp

theorem absorbingGridPoint_eq_mul_step (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (i : Fin (N + 1)) :
    absorbingGridPoint M N hN i = (i : ℝ) * absorbingGridStep M N hN := by
  unfold absorbingGridPoint absorbingGridStep
  ring

theorem absorbingGridPoint_mem (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (i : Fin (N + 1)) :
    absorbingGridPoint M N hN i ∈ absorbingParameterGrid M N hN :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem absorbingParameterGrid_endpoints (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) :
    0 ∈ absorbingParameterGrid M N hN ∧ 1 / (1 - M.discount) ∈ absorbingParameterGrid M N hN := by
  constructor
  · simpa only [absorbingGridPoint_zero] using absorbingGridPoint_mem M N hN ⟨0, by omega⟩
  · simpa only [absorbingGridPoint_last] using absorbingGridPoint_mem M N hN ⟨N, Nat.lt_succ_self N⟩

/-- The parameter grid is deterministic even when applied to the empirical model. -/
theorem absorbingParameterGrid_empirical (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) :
    absorbingParameterGrid (empiricalModel M N hN data) N hN = absorbingParameterGrid M N hN := rfl

/-- The source closed interval is covered, including its right endpoint. -/
theorem absorbingGrid_covers_interval (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount)) :
    ∃ i : Fin (N + 1), |u - absorbingGridPoint M N hN i| ≤ absorbingGridStep M N hN := by
  let D : ℝ := (N : ℝ) * (1 - M.discount)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hD : 0 < D := mul_pos hn hh
  have htu : u * D ≤ N := by
    have hu := (le_div_iff₀ hh).mp hu1
    have hm := mul_le_mul_of_nonneg_left hu hn.le
    dsimp [D]
    nlinarith only [hm]
  let j := ⌊u * D⌋₊
  have hjN : j ≤ N := Nat.floor_le_of_le htu
  let i : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hjN⟩
  have hfloor : (j : ℝ) ≤ u * D := Nat.floor_le (mul_nonneg hu0 hD.le)
  have hsucc : u * D < (j : ℝ) + 1 := Nat.lt_floor_add_one (u * D)
  have hpoint : absorbingGridPoint M N hN i ≤ u := (div_le_iff₀ hD).2 hfloor
  have heq : absorbingGridPoint M N hN i * D = j := by
    change (j : ℝ) / D * D = j
    exact div_mul_cancel₀ _ (ne_of_gt hD)
  refine ⟨i, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hpoint)]
  change u - absorbingGridPoint M N hN i ≤ 1 / D
  apply (le_div_iff₀ hD).2
  nlinarith only [hsucc, heq]

noncomputable def absorbingGridValue (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (x : State) (i : Fin (N + 1)) : State → ℝ :=
  optimalTrajectoryValue (stateAbsorbingModel M x (absorbingGridPoint M N hN i)
    (absorbingGridPoint_bounds M N hN i).1 (absorbingGridPoint_bounds M N hN i).2)

noncomputable def absorbingGridValueFamily (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) : Finset (State → ℝ) :=
  Finset.univ.image (absorbingGridValue M N hN x)

/-- At the absorbing state distinct grid parameters give distinct value vectors. -/
theorem absorbingGridValue_injective (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (x : State) : Function.Injective (absorbingGridValue M N hN x) := by
  intro i j hij
  have hx := congrFun hij x
  change (stateAbsorbingModel M x _ _ _).trajectoryExpectedValue _ x =
    (stateAbsorbingModel M x _ _ _).trajectoryExpectedValue _ x at hx
  rw [stateAbsorbingModel_trajectoryValue_at, stateAbsorbingModel_trajectoryValue_at] at hx
  exact absorbingGridPoint_injective M N hN hx

theorem absorbingGridValueFamily_card (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) : (absorbingGridValueFamily M N hN x).card = N + 1 := by
  rw [absorbingGridValueFamily, Finset.card_image_of_injective _ (absorbingGridValue_injective M N hN x)]
  simp

/-- For any further map of grid indices, duplicate images can only reduce cardinality. -/
theorem absorbingGrid_image_card_le {α : Type*} [DecidableEq α] (N : ℕ) (f : Fin (N + 1) → α) :
    (Finset.univ.image f).card ≤ N + 1 := by
  exact (Finset.card_image_le).trans_eq (by simp)

/-- The source value cover follows from interval coverage, actual value
preservation and the proved fixed-parameter Lipschitz bound. -/
theorem absorbingGrid_covers_optimalValue (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) :
    ∃ i : Fin (N + 1), ‖optimalTrajectoryValue M - absorbingGridValue M N hN x i‖ ≤
      absorbingGridStep M N hN := by
  let u := optimalTrajectoryValue M x
  have hu0 : 0 ≤ u := (M.trajectoryExpectedValue_bounds M.optimalGreedyPolicy x).1
  have hu1 : u ≤ 1 / (1 - M.discount) := (M.trajectoryExpectedValue_bounds M.optimalGreedyPolicy x).2
  obtain ⟨i, hi⟩ := absorbingGrid_covers_interval M N hN u hu0 hu1
  have hp : optimalTrajectoryValue (stateAbsorbingModel M x u hu0 hu1) = optimalTrajectoryValue M := by
    funext s
    exact optimalValueAbsorbingModel_preserves_optimalTrajectoryValue M x s
  have hl := absorbingOptimalValue_parameter_lipschitz M x u (absorbingGridPoint M N hN i)
    hu0 hu1 (absorbingGridPoint_bounds M N hN i).1 (absorbingGridPoint_bounds M N hN i).2
  rw [hp] at hl
  exact ⟨i, hl.trans hi⟩

/-- LemValueCover for the actual sampled empirical model and estimator,
pointwise on every data outcome. The covering index may depend on these data. -/
theorem empirical_absorbingGrid_covers_valueEstimator (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (x : State) :
    ∃ i : Fin (N + 1), ‖valueEstimator M N hN data -
      absorbingGridValue (empiricalModel M N hN data) N hN x i‖ ≤ absorbingGridStep M N hN := by
  have h := absorbingGrid_covers_optimalValue (empiricalModel M N hN data) N hN x
  rw [empirical_optimalTrajectoryValue_eq_valueEstimator] at h
  exact h

/-- A family with at most N+1 points fits the source's beta logarithm after
allocating confidence δ/(2SA). No probability claim is asserted here. -/
theorem absorbingGrid_bernstein_log_bound (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (k : ℕ) (hk0 : 0 < k) (hk : k ≤ N + 1)
    (δ : ℝ) (hδ : 0 < δ) :
    2 * Real.log (4 * k / (δ / (2 * Fintype.card State * Fintype.card Action))) ≤
      2 * Real.log (16 * Fintype.card State * Fintype.card Action * N /
        ((1 - M.discount) * δ)) := by
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let h := 1 - M.discount
  have hS : 0 < S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
  have hkR : (k : ℝ) ≤ 2 * N := by
    exact_mod_cast (hk.trans (by omega : N + 1 ≤ 2 * N))
  have hkh : h * (k : ℝ) ≤ 2 * N :=
    (mul_le_mul_of_nonneg_right hh1 (Nat.cast_nonneg k)).trans (by simpa using hkR)
  have heq : 4 * (k : ℝ) / (δ / (2 * S * A)) = 8 * S * A * k / δ := by field_simp; ring
  change 2 * Real.log (4 * (k : ℝ) / (δ / (2 * S * A))) ≤
    2 * Real.log (16 * S * A * N / (h * δ))
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hδ (mul_pos hh hδ)).2
  have hmul := mul_le_mul_of_nonneg_left hkh (by positivity : 0 ≤ 8 * S * A * δ)
  nlinarith only [hmul]

end StatisticalRL.ModelBasedPolicyLearning
