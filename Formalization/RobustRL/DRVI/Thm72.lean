import Formalization.RobustRL.DRVI.Thm72Numerics
import Formalization.RobustRL.DRVI.Statement

/-!
# Corrected Theorem 7.2 (TV DRVI upper bound), assembly

Plan §3.6–§3.8 for the TV ball: good event over the off-state absorbing family
`[W^b_{x,u_i}]_{α_j}` (`b ∈ {opt, π⋆}`, `i, j ≤ N`), deterministic gap bound on it, constants
`C₁ = 2`, `C₂ = 10⁶`.
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Clipped absorbing family member, as a function of the off-state code of `x`. -/
noncomputable def clipFamily (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (πs : State → Action) (x : State)
    (k : Bool × Fin (N + 1) × Fin (N + 1)) (code : OffStateCode (Action := Action) x N) :
    State → ℝ :=
  fun y ↦ min (absVal ball M N hN σ k.1 πs x ((k.2.1 : ℕ) * gridStep M N)
    (completeOffStateData x N code) y) ((k.2.2 : ℕ) * gridStep M N)

theorem clipFamily_offState (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (πs : State → Action) (x : State)
    (k : Bool × Fin (N + 1) × Fin (N + 1)) (data : Samples State Action N) :
    clipFamily ball M N hN σ πs x k (offStateData x N data) =
      fun y ↦ min (absVal ball M N hN σ k.1 πs x ((k.2.1 : ℕ) * gridStep M N) data y)
        ((k.2.2 : ℕ) * gridStep M N) := by
  unfold clipFamily
  rw [← absVal_offState]

theorem clipFamily_nonneg (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (πs : State → Action) (x : State)
    (k : Bool × Fin (N + 1) × Fin (N + 1)) (code : OffStateCode (Action := Action) x N)
    (y : State) : 0 ≤ clipFamily ball M N hN σ πs x k code y := by
  unfold clipFamily
  exact le_min (absVal_bounds ball M N hN σ hself _ _ _ _ _ y).1
    (mul_nonneg (Nat.cast_nonneg _) (gridStep_pos M hN).le)

theorem clipFamily_le (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (πs : State → Action) (x : State)
    (k : Bool × Fin (N + 1) × Fin (N + 1)) (code : OffStateCode (Action := Action) x N)
    (y : State) : clipFamily ball M N hN σ πs x k code y ≤ 1 / (1 - M.discount) := by
  unfold clipFamily
  exact (min_le_left _ _).trans (absVal_bounds ball M N hN σ hself _ _ _ _ _ y).2

theorem clipFamily_norm_le (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (πs : State → Action) (x : State)
    (k : Bool × Fin (N + 1) × Fin (N + 1)) (code : OffStateCode (Action := Action) x N) :
    ‖clipFamily ball M N hN σ πs x k code‖ ≤ 1 / (1 - M.discount) := by
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  apply norm_le_of_abs_le (by positivity)
  intro y
  rw [abs_of_nonneg (clipFamily_nonneg ball M N hN σ hself πs x k code y)]
  exact clipFamily_le ball M N hN σ hself πs x k code y

/-- Deterministic TV gap bound on the good event. -/
theorem tv_good_gap (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hγpos : 0 < M.discount) (N : ℕ) (hN : 0 < N) (data : Samples State Action N) {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ)
    (hgood : ∀ (x : State) (a : Action) (k : Bool × Fin (N + 1) × Fin (N + 1)),
      |(empiricalRow N hN data x a).expectation
          (clipFamily tvBall M N hN σ (optPolicy (ballFamily tvBall M σ) M) x k
            (offStateData x N data)) -
        (M.transition x a).expectation
          (clipFamily tvBall M N hN σ (optPolicy (ballFamily tvBall M σ) M) x k
            (offStateData x N data))| ≤
        Real.sqrt (2 * ℓ * (M.transition x a).variance
          (clipFamily tvBall M N hN σ (optPolicy (ballFamily tvBall M σ) M) x k
            (offStateData x N data)) / N) +
          2 * (1 / (1 - M.discount)) * ℓ / (3 * N))
    (T : ℕ) (fh : State → Action) (hgreedy : IsGreedy (empiricalDRVI tvBall M σ N hN data T) fh)
    (s : State) :
    robustOptimalValue tvBall M σ s - robustPolicyValue tvBall M σ (detPolicy fh) s ≤
      2 * selfBoundExpr M.discount (1 / (1 - M.discount + M.discount * σ))
          (2 * (M.discount ^ T / (1 - M.discount))) (Real.sqrt (2 * ℓ / N))
          (Real.sqrt (2 * ℓ / N) * (1 / (N * (1 - M.discount)) +
              Real.sqrt (σ * (1 / (1 - M.discount + M.discount * σ)) ^ 2)) +
            2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * (1 / (N * (1 - M.discount)))) +
        2 * (M.discount ^ T / (1 - M.discount)) / (1 - M.discount) := by
  haveI := M.state_nonempty
  have hσ0' : 0 ≤ σ := hσ0.le
  have hself : ∀ p : FiniteDistribution State, p ∈ tvBall p σ := fun p ↦ tvBall_self_mem p hσ0'
  have hatt : ∀ p : FiniteDistribution State, RowAttains (tvBall p σ) :=
    fun p ↦ tvBall_rowAttains p hσ0'
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set πs := optPolicy (ballFamily tvBall M σ) M
  set B' := 1 / (1 - M.discount + M.discount * σ)
  set step := gridStep M N with hstepdef
  have hstep : 0 < step := gridStep_pos M hN
  have hNstep : (N : ℝ) * step = 1 / (1 - M.discount) := N_mul_gridStep M hN
  have hstepeq : step = 1 / (N * (1 - M.discount)) := rfl
  set a1 := Real.sqrt (2 * ℓ / N)
  have ha1 : 0 ≤ a1 := Real.sqrt_nonneg _
  have hspan : ∀ (b : Bool) x y, empVal tvBall M N hN σ b πs data x -
      empVal tvBall M N hN σ b πs data y ≤ B' := by
    intro b x y
    unfold empVal empFam
    cases b
    · exact tv_policyFix_span (empiricalModel M N hN data) hσ0' hσ1 _ x y
    · exact tv_optFix_span (empiricalModel M N hN data) hσ0' hσ1 x y
  rw [← hstepeq]
  apply gap_le tvBall M σ hatt hself N hN data T fh hgreedy hγpos ha1 (by positivity) le_rfl
    (hspan false) (hspan true)
  intro b t a q hq
  obtain ⟨i, hi, hclose⟩ := exists_grid_close tvBall M N hN σ hself b πs t data
  set Y := empVal tvBall M N hN σ b πs data
  set W := absVal tvBall M N hN σ b πs t (i * step) data
  have hW0 : ∀ y, 0 ≤ W y := fun y ↦ (absVal_bounds tvBall M N hN σ hself b πs t _ data y).1
  have hWB : ∀ y, W y ≤ N * step := fun y ↦ by
    rw [hNstep]; exact (absVal_bounds tvBall M N hN σ hself b πs t _ data y).2
  have hbern : ∀ j : ℕ, j ≤ N →
      |(empiricalRow N hN data t a).expectation (fun x ↦ min (W x) (j * step)) -
        (M.transition t a).expectation (fun x ↦ min (W x) (j * step))| ≤
      Real.sqrt (2 * ℓ * (M.transition t a).variance (fun x ↦ min (W x) (j * step)) / N) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) := by
    intro j hj
    have h := hgood t a (b, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
    rw [clipFamily_offState] at h
    exact h
  have hdevY := tv_row_deviation (M.transition t a) (empiricalRow N hN data t a) hσ0 hstep hN hℓ0
    hW0 hWB hNstep hclose hbern
  have htransfer := std_le_of_variance_le (by positivity)
    (tv_variance_transfer hq (hspan b))
  calc _ ≤ a1 * (Real.sqrt ((M.transition t a).variance Y) + step) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * step := hdevY
    _ ≤ a1 * ((Real.sqrt (q.variance Y) + Real.sqrt (σ * B' ^ 2)) + step) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * step := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right htransfer step) ha1
        linarith
    _ = a1 * Real.sqrt (q.variance Y) + (a1 * (step + Real.sqrt (σ * B' ^ 2)) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * step) := by ring

end StatisticalRL.RobustRL.DRVI
