import Formalization.RobustRL.DRVI.Thm74Numerics
import Formalization.RobustRL.DRVI.Thm72

/-!
# Corrected Theorem 7.4 (χ² DRVI upper bound), deterministic part

Good-event family for the χ² ball: the clipped absorbing values `f = [W^b_{x,u_i}]_{α_j}` and
their centered squares `(f − E_{p_{xa}} f)^2` (the latter feed the standard-deviation lemma (S)).
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- χ² family: `c = true` gives the clipped value, `c = false` its centered square under the
true row `P_{x,a}`. -/
noncomputable def chiFamily (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (πs : State → Action) (x : State) (a : Action)
    (k : Bool × Bool × Fin (N + 1) × Fin (N + 1)) (code : OffStateCode (Action := Action) x N) :
    State → ℝ :=
  if k.1 then clipFamily ball M N hN σ πs x k.2 code
  else fun y ↦ (clipFamily ball M N hN σ πs x k.2 code y -
    (M.transition x a).expectation (clipFamily ball M N hN σ πs x k.2 code)) ^ 2

/-- Sup-norm bounds of the χ² family members. -/
noncomputable def chiBound (M : DiscountedMDP State Action) (N : ℕ)
    (k : Bool × Bool × Fin (N + 1) × Fin (N + 1)) : ℝ :=
  if k.1 then 1 / (1 - M.discount) else (1 / (1 - M.discount)) ^ 2

theorem chiFamily_nonneg (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (πs : State → Action) (x : State)
    (a : Action) (k : Bool × Bool × Fin (N + 1) × Fin (N + 1))
    (code : OffStateCode (Action := Action) x N) (y : State) :
    0 ≤ chiFamily ball M N hN σ πs x a k code y := by
  unfold chiFamily
  split_ifs
  · exact clipFamily_nonneg ball M N hN σ hself πs x k.2 code y
  · exact sq_nonneg _

theorem chiFamily_norm_le (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (πs : State → Action) (x : State)
    (a : Action) (k : Bool × Bool × Fin (N + 1) × Fin (N + 1))
    (code : OffStateCode (Action := Action) x N) :
    ‖chiFamily ball M N hN σ πs x a k code‖ ≤ chiBound M N k := by
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have h0 := clipFamily_nonneg ball M N hN σ hself πs x k.2 code
  have h1 := clipFamily_le ball M N hN σ hself πs x k.2 code
  unfold chiFamily chiBound
  split_ifs
  · exact clipFamily_norm_le ball M N hN σ hself πs x k.2 code
  · apply norm_le_of_abs_le (by positivity)
    intro y
    rw [abs_of_nonneg (sq_nonneg _)]
    have hm := expectation_mem_Icc (M.transition x a) h0 h1
    have hy0 := h0 y
    have hy1 := h1 y
    have habs : |clipFamily ball M N hN σ πs x k.2 code y -
        (M.transition x a).expectation (clipFamily ball M N hN σ πs x k.2 code)| ≤
          1 / (1 - M.discount) := by
      rw [abs_le]; constructor <;> linarith [hm.1, hm.2]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- Deterministic χ² gap bound on the good event. -/
theorem chi_good_gap (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 < σ)
    (hγpos : 0 < M.discount) (N : ℕ) (hN : 0 < N) (data : Samples State Action N) {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (hgood : ∀ (x : State) (a : Action) (k : Bool × Bool × Fin (N + 1) × Fin (N + 1)),
      |(empiricalRow N hN data x a).expectation
          (chiFamily chiBall M N hN σ (optPolicy (ballFamily chiBall M σ) M) x a k
            (offStateData x N data)) -
        (M.transition x a).expectation
          (chiFamily chiBall M N hN σ (optPolicy (ballFamily chiBall M σ) M) x a k
            (offStateData x N data))| ≤
        Real.sqrt (2 * ℓ * (M.transition x a).variance
          (chiFamily chiBall M N hN σ (optPolicy (ballFamily chiBall M σ) M) x a k
            (offStateData x N data)) / N) +
          2 * chiBound M N k * ℓ / (3 * N))
    (T : ℕ) (fh : State → Action) (hgreedy : IsGreedy (empiricalDRVI chiBall M σ N hN data T) fh)
    (s : State) :
    robustOptimalValue chiBall M σ s - robustPolicyValue chiBall M σ (detPolicy fh) s ≤
      2 * selfBoundExpr M.discount (1 / (1 - M.discount))
          (2 * (M.discount ^ T / (1 - M.discount))) (Real.sqrt (2 * ℓ / N))
          (Real.sqrt (2 * ℓ / N) * (1 / (N * (1 - M.discount)) +
              Real.sqrt (Real.sqrt σ / 2 * (1 / (1 - M.discount)) ^ 2)) +
            2 * (1 / (1 - M.discount)) * ℓ / (3 * N) +
            Real.sqrt σ * (8 * (1 / (1 - M.discount)) * Real.sqrt (ℓ / N)) +
            (4 + 2 * Real.sqrt σ) * (1 / (N * (1 - M.discount)))) +
        2 * (M.discount ^ T / (1 - M.discount)) / (1 - M.discount) := by
  haveI := M.state_nonempty
  have hσ0' : 0 ≤ σ := hσ0.le
  have hself : ∀ p : FiniteDistribution State, p ∈ chiBall p σ := fun p ↦ chiBall_self_mem p hσ0'
  have hatt : ∀ p : FiniteDistribution State, RowAttains (chiBall p σ) :=
    fun p ↦ chiBall_rowAttains p hσ0'
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set πs := optPolicy (ballFamily chiBall M σ) M
  set B := 1 / (1 - M.discount)
  set step := gridStep M N with hstepdef
  have hstep : 0 < step := gridStep_pos M hN
  have hNstep : (N : ℝ) * step = B := N_mul_gridStep M hN
  have hstepeq : step = 1 / (N * (1 - M.discount)) := rfl
  set a1 := Real.sqrt (2 * ℓ / N)
  have ha1 : 0 ≤ a1 := Real.sqrt_nonneg _
  have hspan : ∀ (b : Bool) x y, empVal chiBall M N hN σ b πs data x -
      empVal chiBall M N hN σ b πs data y ≤ B := by
    intro b x y
    have h1 := (empVal_bounds chiBall M N hN σ hself b πs data x).2
    have h2 := (empVal_bounds chiBall M N hN σ hself b πs data y).1
    linarith
  rw [← hstepeq]
  apply gap_le chiBall M σ hatt hself N hN data T fh hgreedy hγpos ha1 (by positivity) le_rfl
    (hspan false) (hspan true)
  intro b t a q hq
  obtain ⟨i, hi, hclose⟩ := exists_grid_close chiBall M N hN σ hself b πs t data
  set Y := empVal chiBall M N hN σ b πs data
  set W := absVal chiBall M N hN σ b πs t (i * step) data
  have hW0 : ∀ y, 0 ≤ W y := fun y ↦ (absVal_bounds chiBall M N hN σ hself b πs t _ data y).1
  have hWB : ∀ y, W y ≤ N * step := fun y ↦ by
    rw [hNstep]; exact (absVal_bounds chiBall M N hN σ hself b πs t _ data y).2
  have hclip : ∀ j : ℕ, ∀ hj : j ≤ N,
      clipFamily chiBall M N hN σ πs t (b, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
        (offStateData t N data) = fun x ↦ min (W x) (j * step) := by
    intro j hj
    rw [clipFamily_offState]
  have hbern : ∀ j : ℕ, j ≤ N →
      |(empiricalRow N hN data t a).expectation (fun x ↦ min (W x) (j * step)) -
        (M.transition t a).expectation (fun x ↦ min (W x) (j * step))| ≤
      Real.sqrt (2 * ℓ * (M.transition t a).variance (fun x ↦ min (W x) (j * step)) / N) +
        2 * B * ℓ / (3 * N) := by
    intro j hj
    have h := hgood t a (true, b, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
    simp only [chiFamily, chiBound, if_true] at h
    rw [hclip j hj] at h
    exact h
  have hbern2 : ∀ j : ℕ, j ≤ N →
      |(empiricalRow N hN data t a).expectation (fun y ↦ (min (W y) (j * step) -
          (M.transition t a).expectation (fun x ↦ min (W x) (j * step))) ^ 2) -
        (M.transition t a).expectation (fun y ↦ (min (W y) (j * step) -
          (M.transition t a).expectation (fun x ↦ min (W x) (j * step))) ^ 2)| ≤
      Real.sqrt (2 * ℓ * (M.transition t a).variance (fun y ↦ (min (W y) (j * step) -
          (M.transition t a).expectation (fun x ↦ min (W x) (j * step))) ^ 2) / N) +
        2 * B ^ 2 * ℓ / (3 * N) := by
    intro j hj
    have h := hgood t a (false, b, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
    simp only [chiFamily, chiBound, Bool.false_eq_true, if_false] at h
    rw [hclip j hj] at h
    exact h
  have hdevY := chi_row_deviation (M.transition t a) (empiricalRow N hN data t a) hσ0 hstep hN
    hℓ0 hℓN hW0 hWB hNstep hclose hbern hbern2
  have htransfer := std_le_of_variance_le (by positivity)
    (chi_variance_transfer hq (hspan b))
  calc _ ≤ a1 * (Real.sqrt ((M.transition t a).variance Y) + step) + 2 * B * ℓ / (3 * N) +
        Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N)) + (4 + 2 * Real.sqrt σ) * step := hdevY
    _ ≤ a1 * ((Real.sqrt (q.variance Y) + Real.sqrt (Real.sqrt σ / 2 * B ^ 2)) + step) +
        2 * B * ℓ / (3 * N) + Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N)) +
          (4 + 2 * Real.sqrt σ) * step := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right htransfer step) ha1
        linarith
    _ = a1 * Real.sqrt (q.variance Y) + (a1 * (step + Real.sqrt (Real.sqrt σ / 2 * B ^ 2)) +
        2 * B * ℓ / (3 * N) + Real.sqrt σ * (8 * B * Real.sqrt (ℓ / N)) +
          (4 + 2 * Real.sqrt σ) * step) := by ring

end StatisticalRL.RobustRL.DRVI
