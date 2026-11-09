import Formalization.RobustRL.DRVI.Thm74
import Formalization.RobustRL.DRVI.OraclePlanner

/-!
# Oracle planners for the χ² DRVI bound (Remark 7.2, `remark:chi2-upper`)

Source: arXiv:2610.41903v1, `chapters/robust_RL.tex:453–457` (Theorem 7.4 :437–450). The χ²
analogue of `OraclePlanner.lean`: the deterministic χ² gap bound `chi_good_gap` with the DRVI
greediness replaced by a bound `Ξ` on the empirical robust value gap of an arbitrary deterministic
planner output, via the ball-generic `gap_le_of_residual` and `residual_le_valueGap`.

Technical debt: `chi_good_gap_of_valueGap` is a textual copy of `chi_good_gap` with only the
planning hypothesis generalized (as `tv_good_gap_of_valueGap` is for `tv_good_gap`).
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Deterministic χ² gap bound on the good event for an arbitrary deterministic planner output
`fh` whose empirical robust value gap is at most `Ξ` (copy of `chi_good_gap` with the DRVI
greediness replaced by the value-gap requirement, as `tv_good_gap_of_valueGap` does for TV). -/
theorem chi_good_gap_of_valueGap (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 < σ)
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
    (fh : State → Action) {Ξ : ℝ}
    (hgap : ∀ t, robustOptimalValue chiBall (empiricalModel M N hN data) σ t -
      robustPolicyValue chiBall (empiricalModel M N hN data) σ (detPolicy fh) t ≤ Ξ)
    (s : State) :
    robustOptimalValue chiBall M σ s - robustPolicyValue chiBall M σ (detPolicy fh) s ≤
      2 * selfBoundExpr M.discount (1 / (1 - M.discount))
          Ξ (Real.sqrt (2 * ℓ / N))
          (Real.sqrt (2 * ℓ / N) * (1 / (N * (1 - M.discount)) +
              Real.sqrt (Real.sqrt σ / 2 * (1 / (1 - M.discount)) ^ 2)) +
            2 * (1 / (1 - M.discount)) * ℓ / (3 * N) +
            Real.sqrt σ * (8 * (1 / (1 - M.discount)) * Real.sqrt (ℓ / N)) +
            (4 + 2 * Real.sqrt σ) * (1 / (N * (1 - M.discount)))) +
        Ξ / (1 - M.discount) := by
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
  have hres : ∀ t, 0 ≤ optFix (empFam chiBall M N hN σ data) (empiricalModel M N hN data) t -
        robustQ (empFam chiBall M N hN σ data) (empiricalModel M N hN data)
          (optFix (empFam chiBall M N hN σ data) (empiricalModel M N hN data)) t (fh t) ∧
      optFix (empFam chiBall M N hN σ data) (empiricalModel M N hN data) t -
        robustQ (empFam chiBall M N hN σ data) (empiricalModel M N hN data)
          (optFix (empFam chiBall M N hN σ data) (empiricalModel M N hN data)) t (fh t) ≤ Ξ := by
    intro t
    have hr := residual_le_valueGap (empFam chiBall M N hN σ data) (empiricalModel M N hN data)
      (fun s a ↦ ⟨_, hself _⟩) fh t
    have hg := hgap t
    rw [robustOptimalValue_eq_optFix chiBall _ σ (chiBall_family_rowAttains _ hσ0'),
      robustPolicyValue_eq_policyFix chiBall _ σ (chiBall_family_rowAttains _ hσ0')] at hg
    exact ⟨hr.1, hr.2.trans hg⟩
  apply gap_le_of_residual chiBall M σ hatt hself N hN data fh hγpos ha1 (by positivity) hres
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
