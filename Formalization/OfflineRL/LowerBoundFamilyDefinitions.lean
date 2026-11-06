import Formalization.MDP.CoreDefinitions
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Hard MDP family of the offline lower bound (definitions only)

`chapters/offlineRL.tex:2432–2516`: states `{0, 1, …, S-1}` are `Option (Fin m)` with `S = m + 1`
(`none` is state 0, `some i` is state `i + 1`); actions `{0, 1}` are `Bool` (`false` = 0,
`true` = 1). With `δ = 224(1-γ)²ε/γ`, `p = γ + δ`, `q = γ - δ` (`eq:infinite-p-q`) and
`μ(0) = 1 - 1/C`, `μ(s) = 1/(C(S-1))` for `s > 0` (`infinite-mu-assumption`), the transitions
are `eq:defn-Ptheta-defn-inf` and the rewards `eq:defn-r-theta-defn-inf`. The standing assumptions
`2/3 ≤ γ < 1`, `224(1-γ)ε/γ ≤ 1/2` (`eq:infinite-epsilon-assumption`), `C > 2` and `S ≥ 2`
are hypotheses of the construction (`ε ≥ 0` keeps `p, q ∈ [0, 1]`).
-/

open scoped BigOperators
namespace StatisticalRL.OfflineRL.LowerBound

/-- `δ = 224 (1-γ)² ε / γ`. -/
noncomputable def lbGap (γ ε : ℝ) : ℝ := 224 * (1 - γ) ^ 2 * ε / γ

/-- `p = γ + δ`. -/
noncomputable def lbP (γ ε : ℝ) : ℝ := γ + lbGap γ ε

/-- `q = γ - δ`. -/
noncomputable def lbQ (γ ε : ℝ) : ℝ := γ - lbGap γ ε

/-- The state distribution `μ`. -/
noncomputable def lbMu (C : ℝ) (m : ℕ) : Option (Fin m) → ℝ
  | none => 1 - 1 / C
  | some _ => 1 / (C * m)

/-- The row `x · 1{· = o} + (1 - x) · μ` for `0 ≤ x ≤ 1`. -/
noncomputable def lbRow (C : ℝ) (m : ℕ) (hC : 2 < C) (hm : 1 ≤ m) (o : Option (Fin m)) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : FiniteDistribution (Option (Fin m)) where
  prob t := x * (if t = o then 1 else 0) + (1 - x) * lbMu C m t
  prob_nonneg t := by
    have hμ : 0 ≤ lbMu C m t := by
      cases t with
      | none =>
        simp only [lbMu]
        have : 1 / C ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      | some _ =>
        simp only [lbMu]
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity
    have h1 : 0 ≤ 1 - x := by linarith
    have h2 : (0 : ℝ) ≤ (if t = o then 1 else 0) := by split <;> norm_num
    positivity
  sum_prob := by
    have hmR : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      exact this.ne'
    have hC0 : C ≠ 0 := by intro h; rw [h] at hC; norm_num at hC
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ o]
    simp only [Finset.mem_univ, if_true, Fintype.sum_option, lbMu, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- The hard MDP `M_θ` for `θ ∈ {0,1}^{S-1}`. -/
noncomputable def lbMDP (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool) :
    DiscountedMDP (Option (Fin m)) Bool :=
  have hγ0 : 0 < γ := by linarith
  have hgap0 : 0 ≤ lbGap γ ε := by
    unfold lbGap; exact div_nonneg (by positivity) hγ0.le
  have hgap1 : lbGap γ ε ≤ (1 - γ) / 2 := by
    have h : lbGap γ ε = (1 - γ) * (224 * (1 - γ) * ε / γ) := by unfold lbGap; ring
    rw [h]
    have := mul_le_mul_of_nonneg_left hεmax (by linarith : (0 : ℝ) ≤ 1 - γ)
    linarith
  { state_nonempty := ⟨none⟩
    action_nonempty := ⟨false⟩
    transition := fun o a =>
      match o with
      | none =>
        if a then lbRow C m hC hm none (2 * γ - 1) (by linarith) (by linarith)
        else lbRow C m hC hm none 1 (by norm_num) le_rfl
      | some i =>
        if a = θ i then
          lbRow C m hC hm (some i) (lbP γ ε) (by unfold lbP; linarith)
            (by unfold lbP; linarith)
        else
          lbRow C m hC hm (some i) (lbQ γ ε) (by unfold lbQ; linarith)
            (by unfold lbQ; linarith)
    reward := fun o a =>
      match o with
      | none => if a then 0 else 4 / 7
      | some _ => 1
    reward_nonneg := by
      intro o a
      cases o with
      | none => cases a <;> norm_num
      | some _ => norm_num
    reward_le_one := by
      intro o a
      cases o with
      | none => cases a <;> norm_num
      | some _ => norm_num
    discount := γ
    discount_nonneg := hγ0.le
    discount_lt_one := hγ1 }

end StatisticalRL.OfflineRL.LowerBound
