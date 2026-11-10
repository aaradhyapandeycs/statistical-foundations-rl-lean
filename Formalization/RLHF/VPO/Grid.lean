import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corrected Theorem 7.12: grid cover of the parameter ball

Grid cover: with `M = ⌈2 R T √d⌉₊` cells of side `2R/M` per
coordinate, every `θ` with `‖θ‖ ≤ R` lies within `1/T` of the representative of its cell, and the
representative is in the ball. There are `M^d` cells.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

/-- Number of cells per coordinate, `M = ⌈2 R T √d⌉₊`. -/
noncomputable def gridM (R : ℝ) (T d : ℕ) : ℕ := ⌈2 * R * T * √(d : ℝ)⌉₊

/-- Cell index of a coordinate value `t` (clamped to `M − 1`). -/
noncomputable def cellIdx (R : ℝ) (M : ℕ) (t : ℝ) : ℕ := min (M - 1) ⌊(t + R) / (2 * R / M)⌋₊

theorem cellIdx_bounds {R : ℝ} {M : ℕ} {t : ℝ} (hR : 0 < R) (hM : 1 ≤ M) (ht : |t| ≤ R) :
    (cellIdx R M t : ℝ) ≤ (t + R) / (2 * R / M) ∧
      (t + R) / (2 * R / M) ≤ (cellIdx R M t : ℝ) + 1 := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hh : 0 < 2 * R / M := div_pos (by linarith) hMR
  set u := (t + R) / (2 * R / M)
  have hu0 : 0 ≤ u := div_nonneg (by linarith [neg_abs_le t]) hh.le
  have huM : u ≤ M := by
    rw [div_le_iff₀ hh]
    have : (M : ℝ) * (2 * R / M) = 2 * R := by field_simp
    rw [this]; linarith [le_abs_self t]
  have hfl := Nat.floor_le hu0
  have hfl2 := Nat.lt_floor_add_one u
  unfold cellIdx
  rcases le_total ⌊u⌋₊ (M - 1) with h | h
  · rw [min_eq_right h]
    exact ⟨hfl, hfl2.le⟩
  · rw [min_eq_left h]
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM]; simp
    have h' : ((M - 1 : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast h
    constructor
    · linarith
    · rw [hM1]; linarith

theorem cellIdx_lt {R : ℝ} {M : ℕ} (hM : 1 ≤ M) (t : ℝ) : cellIdx R M t < M :=
  lt_of_le_of_lt (min_le_left _ _) (by omega)

variable {d : ℕ}

theorem abs_apply_le_norm (θ : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |θ i| ≤ ‖θ‖ := by
  have h := EuclideanSpace.norm_sq_eq θ
  have hi : ‖θ i‖ ^ 2 ≤ ∑ j, ‖θ j‖ ^ 2 :=
    single_le_sum (f := fun j ↦ ‖θ j‖ ^ 2) (fun j _ ↦ sq_nonneg _) (mem_univ i)
  rw [← h, Real.norm_eq_abs] at hi
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 hi

/-- Cell of `θ` in the grid with `M` cells per coordinate. -/
noncomputable def gridCell (R : ℝ) (M : ℕ) (hM : 1 ≤ M) (θ : EuclideanSpace ℝ (Fin d)) :
    Fin d → Fin M :=
  fun i ↦ ⟨cellIdx R M (θ i), cellIdx_lt hM _⟩

open Classical in
/-- Representative of a cell: some point of the ball in the cell (or `0` if there is none). -/
noncomputable def gridRep (R : ℝ) (M : ℕ) (hM : 1 ≤ M) (c : Fin d → Fin M) :
    EuclideanSpace ℝ (Fin d) :=
  if h : ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ R ∧ gridCell R M hM θ = c then h.choose else 0

theorem gridRep_norm_le {R : ℝ} (hR : 0 ≤ R) {M : ℕ} (hM : 1 ≤ M) (c : Fin d → Fin M) :
    ‖gridRep R M hM c‖ ≤ R := by
  unfold gridRep
  split_ifs with h
  · exact h.choose_spec.1
  · simpa using hR

theorem one_le_gridM {R : ℝ} (hR : 0 < R) {T : ℕ} (hT : 1 ≤ T) (hd : 0 < d) :
    1 ≤ gridM R T d := by
  unfold gridM
  have : (0 : ℝ) < 2 * R * T * √(d : ℝ) := by
    have : (0 : ℝ) < T := by exact_mod_cast hT
    have : (0 : ℝ) < √(d : ℝ) := sqrt_pos.2 (by exact_mod_cast hd)
    positivity
  exact Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)

/-- Grid cover: the representative of the cell of `θ` is in the ball and within `1/T`. -/
theorem gridRep_cover {R : ℝ} (hR : 0 < R) {T : ℕ} (hT : 1 ≤ T) (hd : 0 < d)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ ≤ R) :
    ‖θ - gridRep R (gridM R T d) (one_le_gridM hR hT hd)
        (gridCell R (gridM R T d) (one_le_gridM hR hT hd) θ)‖ ≤ 1 / T := by
  set M := gridM R T d
  have hM := one_le_gridM hR hT hd
  set c := gridCell R M hM θ
  have hex : ∃ θ' : EuclideanSpace ℝ (Fin d), ‖θ'‖ ≤ R ∧ gridCell R M hM θ' = c := ⟨θ, hθ, rfl⟩
  have hrep : gridRep R M hM c = hex.choose := by unfold gridRep; rw [dif_pos hex]
  rw [hrep]
  set θ' := hex.choose
  have hθ' : ‖θ'‖ ≤ R := hex.choose_spec.1
  have hc' : gridCell R M hM θ' = c := hex.choose_spec.2
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 hM
  set h := 2 * R / M
  have hh : 0 < h := div_pos (by linarith) hMR
  have hcoord : ∀ i, |θ i - θ' i| ≤ h := by
    intro i
    have hidx : cellIdx R M (θ i) = cellIdx R M (θ' i) := by
      have := congrFun hc' i
      simp only [c, gridCell, Fin.mk.injEq] at this
      exact this.symm
    have b1 : (cellIdx R M (θ' i) : ℝ) ≤ (θ i + R) / h ∧
        (θ i + R) / h ≤ (cellIdx R M (θ' i) : ℝ) + 1 := by
      have := cellIdx_bounds hR hM (le_trans (abs_apply_le_norm θ i) hθ)
      rw [hidx] at this; exact this
    have b2 : (cellIdx R M (θ' i) : ℝ) ≤ (θ' i + R) / h ∧
        (θ' i + R) / h ≤ (cellIdx R M (θ' i) : ℝ) + 1 :=
      cellIdx_bounds hR hM (le_trans (abs_apply_le_norm θ' i) hθ')
    have hdiff : |(θ i + R) / h - (θ' i + R) / h| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
    have : (θ i + R) / h - (θ' i + R) / h = (θ i - θ' i) / h := by ring
    rw [this, abs_div, abs_of_pos hh, div_le_one hh] at hdiff
    exact hdiff
  -- `h ≤ 1/(T √d)`
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsd : (0 : ℝ) < √(d : ℝ) := sqrt_pos.2 (by exact_mod_cast hd)
  have hMge : 2 * R * T * √(d : ℝ) ≤ M := Nat.le_ceil _
  have hhle : h * (T * √(d : ℝ)) ≤ 1 := by
    simp only [h]
    rw [div_mul_eq_mul_div, div_le_one hMR]
    linarith
  clear_value h
  have hfin : (d : ℝ) * h ^ 2 ≤ (1 / T) ^ 2 := by
    have h2 : (h * (T * √(d : ℝ))) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hhle
    have h3 : (h * (T * √(d : ℝ))) ^ 2 = d * h ^ 2 * T ^ 2 := by
      rw [mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg _)]; ring
    rw [h3] at h2
    rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    exact h2
  have hsq : ‖θ - θ'‖ ^ 2 ≤ (1 / T) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(θ - θ') i‖ ^ 2 ≤ ∑ _i : Fin d, h ^ 2 := sum_le_sum fun i _ ↦ by
          rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          have := hcoord i
          have h0 := abs_nonneg (θ i - θ' i)
          nlinarith [sq_abs (θ i - θ' i)]
      _ = d * h ^ 2 := by simp
      _ ≤ (1 / T) ^ 2 := hfin
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

end StatisticalRL.Ch7Rest.Rlhf
