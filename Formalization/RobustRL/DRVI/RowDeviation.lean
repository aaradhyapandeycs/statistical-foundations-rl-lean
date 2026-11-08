import Formalization.RobustRL.DRVI.DualDeviation

/-!
# Per-row deviation bound at a data-dependent value vector (milestone 4/5, plan §3.7 Steps 1–2)

Let `Y` be within `step` (sup norm) of a vector `W` with `0 ≤ W ≤ N·step = B`, and assume the
Bernstein inequalities for the clipped vectors `[W]_{α_j}` (and, for χ², for their centered
squares). Then
* TV: `|g_{p̂}(Y) − g_p(Y)| ≤ √(2ℓ/N)(std_p Y + step) + 2Bℓ/(3N) + 4·step`;
* χ²: `|g_{p̂}(Y) − g_p(Y)| ≤ √(2ℓ/N)(std_p Y + step) + 2Bℓ/(3N) + 8√σ B √(ℓ/N)
  + (4 + 2√σ)·step` (needs `ℓ ≤ N`).
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State : Type*} [Fintype State]

theorem norm_le_of_abs_le {V : State → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, |V x| ≤ c) :
    ‖V‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 (fun x ↦ by rw [Real.norm_eq_abs]; exact h x)

theorem sqrt_two_mul_div (ℓ v N : ℝ) (hℓ : 0 ≤ ℓ) (_hv : 0 ≤ v) (hN : 0 ≤ N) :
    Real.sqrt (2 * ℓ * v / N) = Real.sqrt (2 * ℓ / N) * Real.sqrt v := by
  rw [show 2 * ℓ * v / N = (2 * ℓ / N) * v by ring, Real.sqrt_mul (by positivity)]

variable [Nonempty State]

/-- TV per-row deviation at `Y`. -/
theorem tv_row_deviation (p p' : FiniteDistribution State) {Y W : State → ℝ} {σ step ℓ B : ℝ}
    {N : ℕ} (hσ : 0 < σ) (hstep : 0 < step) (hNpos : 0 < N) (hℓ : 0 ≤ ℓ)
    (hW0 : ∀ s, 0 ≤ W s) (hWB : ∀ s, W s ≤ N * step) (hB : (N : ℝ) * step = B)
    (hYW : ∀ s, |Y s - W s| ≤ step)
    (hbern : ∀ j : ℕ, j ≤ N →
      |p'.expectation (fun x ↦ min (W x) (j * step)) - p.expectation (fun x ↦ min (W x) (j * step))|
        ≤ Real.sqrt (2 * ℓ * p.variance (fun x ↦ min (W x) (j * step)) / N) +
          2 * B * ℓ / (3 * N)) :
    |rowInf (tvBall p' σ) Y - rowInf (tvBall p σ) Y| ≤
      Real.sqrt (2 * ℓ / N) * (Real.sqrt (p.variance Y) + step) + 2 * B * ℓ / (3 * N) +
        4 * step := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hnorm : ‖Y - W‖ ≤ step := norm_le_of_abs_le hstep.le (fun x ↦ by simpa using hYW x)
  have h1 := abs_rowInf_sub_le (tvBall p' σ) hstep.le hYW
  have h2 := abs_rowInf_sub_le (tvBall p σ) hstep.le hYW
  have hstdW : Real.sqrt (p.variance W) ≤ Real.sqrt (p.variance Y) + step :=
    FiniteDistribution.sqrt_variance_le_of_norm_sub_le p Y W step hnorm
  set c := Real.sqrt (2 * ℓ / N) * Real.sqrt (p.variance W) + 2 * B * ℓ / (3 * N)
  have hc : ∀ j : ℕ, j ≤ N →
      |p'.expectation (fun x ↦ min (W x) (j * step)) -
        p.expectation (fun x ↦ min (W x) (j * step))| ≤ c := by
    intro j hj
    refine (hbern j hj).trans ?_
    refine add_le_add ?_ le_rfl
    rw [sqrt_two_mul_div ℓ _ N hℓ (FiniteDistribution.variance_nonneg _ _) hNR.le]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt (variance_min_le p W _)
  have hT := tv_rowInf_deviation p p' hW0 hσ hstep hWB hc
  have hcle : c ≤ Real.sqrt (2 * ℓ / N) * (Real.sqrt (p.variance Y) + step) +
      2 * B * ℓ / (3 * N) := by
    refine add_le_add ?_ le_rfl
    exact mul_le_mul_of_nonneg_left hstdW (Real.sqrt_nonneg _)
  have e : rowInf (tvBall p' σ) Y - rowInf (tvBall p σ) Y =
      (rowInf (tvBall p' σ) Y - rowInf (tvBall p' σ) W) +
        (rowInf (tvBall p' σ) W - rowInf (tvBall p σ) W) +
          (rowInf (tvBall p σ) W - rowInf (tvBall p σ) Y) := by ring
  rw [e]
  calc _ ≤ |rowInf (tvBall p' σ) Y - rowInf (tvBall p' σ) W| +
        |rowInf (tvBall p' σ) W - rowInf (tvBall p σ) W| +
          |rowInf (tvBall p σ) W - rowInf (tvBall p σ) Y| := abs_add_three _ _ _
    _ ≤ step + (c + 2 * step) + step := by
        rw [abs_sub_comm (rowInf (tvBall p σ) W)]
        exact add_le_add (add_le_add h1 hT) h2
    _ ≤ _ := by linarith

/-- χ² per-row deviation at `Y`. -/
theorem chi_row_deviation (p p' : FiniteDistribution State) {Y W : State → ℝ} {σ step ℓ B : ℝ}
    {N : ℕ} (hσ : 0 < σ) (hstep : 0 < step) (hNpos : 0 < N) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (hW0 : ∀ s, 0 ≤ W s) (hWB : ∀ s, W s ≤ N * step) (hB : (N : ℝ) * step = B)
    (hYW : ∀ s, |Y s - W s| ≤ step)
    (hbern : ∀ j : ℕ, j ≤ N →
      |p'.expectation (fun x ↦ min (W x) (j * step)) - p.expectation (fun x ↦ min (W x) (j * step))|
        ≤ Real.sqrt (2 * ℓ * p.variance (fun x ↦ min (W x) (j * step)) / N) +
          2 * B * ℓ / (3 * N))
    (hbern2 : ∀ j : ℕ, j ≤ N →
      |p'.expectation (fun y ↦ (min (W y) (j * step) -
          p.expectation (fun x ↦ min (W x) (j * step))) ^ 2) -
        p.expectation (fun y ↦ (min (W y) (j * step) -
          p.expectation (fun x ↦ min (W x) (j * step))) ^ 2)|
        ≤ Real.sqrt (2 * ℓ * p.variance (fun y ↦ (min (W y) (j * step) -
            p.expectation (fun x ↦ min (W x) (j * step))) ^ 2) / N) +
          2 * B ^ 2 * ℓ / (3 * N)) :
    |rowInf (chiBall p' σ) Y - rowInf (chiBall p σ) Y| ≤
      Real.sqrt (2 * ℓ / N) * (Real.sqrt (p.variance Y) + step) + 2 * B * ℓ / (3 * N) +
        Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N)) + (4 + 2 * Real.sqrt σ) * step := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hB0 : 0 ≤ B := by rw [← hB]; positivity
  have hnorm : ‖Y - W‖ ≤ step := norm_le_of_abs_le hstep.le (fun x ↦ by simpa using hYW x)
  have h1 := abs_rowInf_sub_le (chiBall p' σ) hstep.le hYW
  have h2 := abs_rowInf_sub_le (chiBall p σ) hstep.le hYW
  have hstdW : Real.sqrt (p.variance W) ≤ Real.sqrt (p.variance Y) + step :=
    FiniteDistribution.sqrt_variance_le_of_norm_sub_le p Y W step hnorm
  have hsσ : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
  set c := (Real.sqrt (2 * ℓ / N) * Real.sqrt (p.variance W) + 2 * B * ℓ / (3 * N)) +
    Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N))
  have hc : ∀ j : ℕ, j ≤ N →
      |p'.expectation (fun x ↦ min (W x) (j * step)) -
          p.expectation (fun x ↦ min (W x) (j * step))| +
        Real.sqrt σ * |Real.sqrt (p'.variance (fun x ↦ min (W x) (j * step))) -
          Real.sqrt (p.variance (fun x ↦ min (W x) (j * step)))| ≤ c := by
    intro j hj
    set f : State → ℝ := fun x ↦ min (W x) (j * step)
    have hf0 : ∀ x, 0 ≤ f x := fun x ↦ le_min (hW0 x) (by positivity)
    have hfB : ∀ x, f x ≤ B := fun x ↦ (min_le_left _ _).trans (hB ▸ hWB x)
    have hmean : |p'.expectation f - p.expectation f| ≤
        Real.sqrt (2 * ℓ / N) * Real.sqrt (p.variance W) + 2 * B * ℓ / (3 * N) := by
      refine (hbern j hj).trans ?_
      refine add_le_add ?_ le_rfl
      rw [sqrt_two_mul_div ℓ _ N hℓ (FiniteDistribution.variance_nonneg _ _) hNR.le]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact Real.sqrt_le_sqrt (variance_min_le p W _)
    have hS := std_deviation_le p p' hB0 hf0 hfB hNR hℓ hℓN (hbern j hj) (by
      refine (hbern2 j hj).trans ?_
      refine add_le_add ?_ le_rfl
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ hNR.le
      have := variance_centeredSq_le p hf0 hfB
      have h2l : 0 ≤ 2 * ℓ := by positivity
      nlinarith)
    calc _ ≤ (Real.sqrt (2 * ℓ / N) * Real.sqrt (p.variance W) + 2 * B * ℓ / (3 * N)) +
          Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N)) :=
          add_le_add hmean (mul_le_mul_of_nonneg_left hS hsσ)
      _ = c := rfl
  have hX := chi_rowInf_deviation p p' hW0 hσ hstep hWB hc
  have hcle : c ≤ (Real.sqrt (2 * ℓ / N) * (Real.sqrt (p.variance Y) + step) +
      2 * B * ℓ / (3 * N)) + Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N)) := by
    refine add_le_add ?_ le_rfl
    refine add_le_add ?_ le_rfl
    exact mul_le_mul_of_nonneg_left hstdW (Real.sqrt_nonneg _)
  have e : rowInf (chiBall p' σ) Y - rowInf (chiBall p σ) Y =
      (rowInf (chiBall p' σ) Y - rowInf (chiBall p' σ) W) +
        (rowInf (chiBall p' σ) W - rowInf (chiBall p σ) W) +
          (rowInf (chiBall p σ) W - rowInf (chiBall p σ) Y) := by ring
  rw [e]
  calc _ ≤ |rowInf (chiBall p' σ) Y - rowInf (chiBall p' σ) W| +
        |rowInf (chiBall p' σ) W - rowInf (chiBall p σ) W| +
          |rowInf (chiBall p σ) W - rowInf (chiBall p σ) Y| := abs_add_three _ _ _
    _ ≤ step + (c + (2 + 2 * Real.sqrt σ) * step) + step := by
        rw [abs_sub_comm (rowInf (chiBall p σ) W)]
        exact add_le_add (add_le_add h1 hX) h2
    _ ≤ _ := by linarith

end StatisticalRL.RobustRL.DRVI
