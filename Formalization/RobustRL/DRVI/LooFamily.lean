import Formalization.RobustRL.DRVI.GoodEvent
import Formalization.RobustRL.DRVI.SelfBound

/-!
# Leave-one-out absorbing values on the empirical model (milestone 4, plan §3.5 facts 1–4)

For the empirical ball family `Û(data)` and a fixed data-free selector `f` (the true optimal
policy `π⋆`), `absVal b f x u data` is the absorbing robust optimal value (`b = true`) or the
absorbing robust value of `f` (`b = false`). It depends only on the samples at states `≠ x`
(`absVal_offState`), is 1-Lipschitz in `u`, lies in `[0, 1/(1−γ)]`, and coincides with the
empirical value `empVal b f data` at `u = empVal b f data x`. Hence every empirical value is
within `step = 1/(N(1−γ))` of a grid member `u_i = i·step`, `i ≤ N` (`exists_grid_close`).
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The empirical ball family `Û(data) s a = ball (P̂_{s,a}) σ`. -/
noncomputable def empFam (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (data : Samples State Action N) : RowFamily State Action :=
  ballFamily ball (empiricalModel M N hN data) σ

/-- Empirical robust values: optimal (`true`) or of the fixed selector `f` (`false`). -/
noncomputable def empVal (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (b : Bool) (f : State → Action) (data : Samples State Action N) :
    State → ℝ :=
  if b then optFix (empFam ball M N hN σ data) (empiricalModel M N hN data)
  else policyFix (empFam ball M N hN σ data) (empiricalModel M N hN data) (detPolicy f)

/-- Absorbing leave-one-out values. -/
noncomputable def absVal (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (b : Bool) (f : State → Action) (x : State) (u : ℝ)
    (data : Samples State Action N) : State → ℝ :=
  if b then optFix (absorbFamily (empFam ball M N hN σ data) x) (absorbMDP M x u)
  else policyFix (absorbFamily (empFam ball M N hN σ data) x) (absorbMDP M x u) (detPolicy f)

/-- The grid step `1/(N(1−γ))`. -/
noncomputable def gridStep (M : DiscountedMDP State Action) (N : ℕ) : ℝ :=
  1 / (N * (1 - M.discount))

theorem gridStep_pos (M : DiscountedMDP State Action) {N : ℕ} (hN : 0 < N) :
    0 < gridStep M N := by
  have : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold gridStep; positivity

theorem N_mul_gridStep (M : DiscountedMDP State Action) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * gridStep M N = 1 / (1 - M.discount) := by
  have : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold gridStep; field_simp

theorem empFam_offState (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (x : State) (data : Samples State Action N) :
    absorbFamily (empFam ball M N hN σ data) x =
      absorbFamily (empFam ball M N hN σ (completeOffStateData x N (offStateData x N data))) x := by
  classical
  funext s a
  unfold absorbFamily
  by_cases hs : s = x
  · simp [hs]
  · simp only [hs, if_false]
    show ball (empiricalRow N hN data s a) σ =
      ball (empiricalRow N hN (completeOffStateData x N (offStateData x N data)) s a) σ
    congr 1
    unfold empiricalRow
    congr 1
    funext i
    simp [completeOffStateData, offStateData, hs]

theorem absVal_offState (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (b : Bool) (f : State → Action) (x : State) (u : ℝ)
    (data : Samples State Action N) :
    absVal ball M N hN σ b f x u data =
      absVal ball M N hN σ b f x u (completeOffStateData x N (offStateData x N data)) := by
  unfold absVal
  rw [empFam_offState ball M N hN σ x data]

theorem empFam_nonempty (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (data : Samples State Action N) :
    ∀ s a, (empFam ball M N hN σ data s a).Nonempty :=
  fun _ _ ↦ ⟨_, hself _⟩

theorem absVal_bounds (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (b : Bool) (f : State → Action)
    (x : State) (u : ℝ) (data : Samples State Action N) (s : State) :
    0 ≤ absVal ball M N hN σ b f x u data s ∧
      absVal ball M N hN σ b f x u data s ≤ 1 / (1 - M.discount) := by
  have hne := absorbFamily_nonempty _ (empFam_nonempty ball M N hN σ hself data) x
  unfold absVal
  cases b
  · exact policyFix_bounds _ hne (absorbMDP M x u) _ s
  · exact optFix_bounds _ hne (absorbMDP M x u) s

theorem empVal_bounds (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (b : Bool) (f : State → Action)
    (data : Samples State Action N) (s : State) :
    0 ≤ empVal ball M N hN σ b f data s ∧
      empVal ball M N hN σ b f data s ≤ 1 / (1 - M.discount) := by
  have hne := empFam_nonempty ball M N hN σ hself data
  unfold empVal
  cases b
  · exact policyFix_bounds _ hne _ _ s
  · exact optFix_bounds _ hne _ s

theorem absVal_lipschitz (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (b : Bool) (f : State → Action) (x : State) (u u' : ℝ)
    (data : Samples State Action N) (s : State) :
    |absVal ball M N hN σ b f x u data s - absVal ball M N hN σ b f x u' data s| ≤ |u - u'| := by
  unfold absVal
  cases b
  · exact absorb_policyFix_lipschitz _ M x f u u' s
  · exact absorb_optFix_lipschitz _ M x u u' s

theorem absVal_coincide (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (b : Bool) (f : State → Action)
    (x : State) (data : Samples State Action N) :
    absVal ball M N hN σ b f x (empVal ball M N hN σ b f data x) data =
      empVal ball M N hN σ b f data := by
  have hne := empFam_nonempty ball M N hN σ hself data
  have hcongr : ∀ u, (absorbMDP (empiricalModel M N hN data) x u).reward =
      (absorbMDP M x u).reward := fun u ↦ rfl
  unfold absVal empVal
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [← policyFix_congr _ (hcongr _) rfl]
    exact absorb_policyFix_eq _ hne _ x f
  · simp only [if_true]
    rw [← optFix_congr _ (hcongr _) rfl]
    exact absorb_optFix_eq _ hne _ x

/-- Grid cover (plan §3.5 fact 3). -/
theorem exists_grid_close (ball : RowBall State) (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (σ : ℝ) (hself : ∀ p, p ∈ ball p σ) (b : Bool) (f : State → Action)
    (x : State) (data : Samples State Action N) :
    ∃ i : ℕ, i ≤ N ∧ ∀ s, |empVal ball M N hN σ b f data s -
      absVal ball M N hN σ b f x (i * gridStep M N) data s| ≤ gridStep M N := by
  have hb := empVal_bounds ball M N hN σ hself b f data x
  obtain ⟨i, hi, hclose⟩ := exists_net_point (gridStep_pos M hN) hb.1
    (by rw [N_mul_gridStep M hN]; exact hb.2)
  refine ⟨i, hi, fun s ↦ ?_⟩
  have := absVal_lipschitz ball M N hN σ b f x (empVal ball M N hN σ b f data x)
    (i * gridStep M N) data s
  rw [absVal_coincide ball M N hN σ hself b f x data] at this
  exact this.trans hclose

end StatisticalRL.RobustRL.DRVI
