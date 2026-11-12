import Formalization.RobustRL.DRVI.Thm74Main
import Formalization.RobustRL.DRVI.OraclePlannerChi
import Formalization.RobustRL.DRVI.OraclePlannerChiNumerics

/-!
# Restricted Remark 7.2 (`remark:chi2-upper`), final library statement

Source: arXiv:2610.41903v1, `chapters/robust_RL.tex:453–457` (Theorem 7.4 :437–450).
For every `c_opt ≥ 0`, `c₂ = 10⁶ + 8 c_opt` works. The single-action case (`A = 1`) is trivial:
there is one deterministic policy, so the gap is `0`. Otherwise `SA ≥ 2`, and the planner error
`Ξ = c_opt log(SAN/((1−γ)δ))/N²` meets `Ξ ≤ 1` and `Ξ/(1−γ) ≤ ε/2`
(`chi_oracle_planning_bounds`), which feed `chi_selfBoundExpr_le_of_planning`.
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

local instance chiOracleMainStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Restricted Remark 7.2: for every `c_opt ≥ 0` there is `c₂ > 0` (namely `10⁶ + 8 c_opt`)
such that, under the sample-size condition of Theorem 7.4, with probability at least `1−δ` every
deterministic planner output `f` with empirical χ²-robust value gap at most
`c_opt log(SAN/((1−γ)δ))/N²` (in absolute value, at every state) is `ε`-optimal for the true
χ²-robust MDP. -/
theorem chi_oracle_planner_guarantee :
  ∀ c_opt : ℝ, 0 ≤ c_opt → ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      0 < σ → 1 / 4 ≤ M.discount → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ 1 / (1 - M.discount) →
      c₂ / ((1 - M.discount) ^ 3 * ε ^ 2) *
          (1 + max (Real.sqrt σ) σ / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N →
      1 - δ ≤ (samplingLaw M N).real
        {data | ∀ f : State → Action,
          (∀ s, |robustOptimalValue chiBall (empiricalModel M N hN data) σ s -
              robustPolicyValue chiBall (empiricalModel M N hN data) σ (detPolicy f) s| ≤
            c_opt / (N : ℝ) ^ 2 *
              Real.log (Fintype.card State * Fintype.card Action * N /
                ((1 - M.discount) * δ))) →
          ∀ s, robustOptimalValue chiBall M σ s -
            robustPolicyValue chiBall M σ (detPolicy f) s ≤ ε} := by
  intro c_opt hc
  refine ⟨10 ^ 6 + 8 * c_opt, by positivity, ?_⟩
  intro State Action _ _ M σ δ ε N hN hσ0 hγ hδ0 hδ1 hε0 hεg hsample
  classical
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  have hγ1 := M.discount_lt_one
  have hg : 0 < 1 - M.discount := by linarith
  have hγpos : 0 < M.discount := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- single-action case
  by_cases hA1 : Fintype.card Action ≤ 1
  · haveI : Subsingleton Action := Fintype.card_le_one_iff_subsingleton.mp hA1
    have hσ0' : 0 ≤ σ := hσ0.le
    have hU : ∀ s a, RowAttains (chiBall (M.transition s a) σ) :=
      chiBall_family_rowAttains M hσ0'
    have hall : {data : Samples State Action N | ∀ f : State → Action,
        (∀ s, |robustOptimalValue chiBall (empiricalModel M N hN data) σ s -
            robustPolicyValue chiBall (empiricalModel M N hN data) σ (detPolicy f) s| ≤
          c_opt / (N : ℝ) ^ 2 *
            Real.log (Fintype.card State * Fintype.card Action * N /
              ((1 - M.discount) * δ))) →
        ∀ s, robustOptimalValue chiBall M σ s -
          robustPolicyValue chiBall M σ (detPolicy f) s ≤ ε} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro f _ s
      rw [robustOptimalValue_eq_robustPolicyValue_optPolicy chiBall M σ hU]
      have : optPolicy (ballFamily chiBall M σ) M = f :=
        deterministic_policy_eq_of_subsingleton _ _
      rw [this, sub_self]
      exact hε0.le
    rw [hall, probReal_univ]
    linarith
  push_neg at hA1
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hA2 : (2 : ℝ) ≤ Fintype.card Action := by exact_mod_cast hA1
  have hSA : (2 : ℝ) ≤ Fintype.card State * Fintype.card Action :=
    le_trans hA2 (le_mul_of_one_le_left (by linarith) hS)
  have hL2 := chi_L_lower hSA hN1 hδ0 hδ1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hL : 1 / 2 ≤ Real.log (Fintype.card State * Fintype.card Action * N / δ) := by
    linarith
  set πs := optPolicy (ballFamily chiBall M σ) M
  have hself : ∀ p : FiniteDistribution State, p ∈ chiBall p σ :=
    fun p ↦ chiBall_self_mem p hσ0.le
  have hG : ∀ (x : State) (a : Action) (k : Bool × Bool × Fin (N + 1) × Fin (N + 1))
      (c : OffStateCode (Action := Action) x N) (y : State),
      0 ≤ chiFamily chiBall M N hN σ πs x a k c y :=
    fun x a k c y ↦ chiFamily_nonneg chiBall M N hN σ hself πs x a k c y
  have hGB : ∀ (x : State) (a : Action) (k : Bool × Bool × Fin (N + 1) × Fin (N + 1))
      (c : OffStateCode (Action := Action) x N),
      ‖chiFamily chiBall M N hN σ πs x a k c‖ ≤ chiBound M N k :=
    fun x a k c ↦ chiFamily_norm_le chiBall M N hN σ hself πs x a k c
  have hprob := allRows_indexed_bernstein' (ι := Bool × Bool × Fin (N + 1) × Fin (N + 1)) M N hN
    (fun x a k c ↦ chiFamily chiBall M N hN σ πs x a k c) hG (chiBound M N) hGB δ hδ0 hδ1
  have hcard : ((Fintype.card (Bool × Bool × Fin (N + 1) × Fin (N + 1)) : ℕ) : ℝ) =
      4 * (N + 1) ^ 2 := by
    simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]; ring
  set ℓ := Real.log (4 * ((Fintype.card (Bool × Bool × Fin (N + 1) × Fin (N + 1)) : ℕ) : ℝ) *
    ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ)) / δ) with hℓdef
  have hℓ : ℓ ≤ 9 * Real.log (Fintype.card State * Fintype.card Action * N / δ) := by
    rw [hℓdef, hcard]
    exact chi_ell_le hSA hN1 hδ0 hδ1
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef, hcard]
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have hN2 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    have h3 := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 4) (by linarith : (1 : ℝ) ≤ 4 * ((N : ℝ) + 1) ^ 2))
      (by linarith : (1 : ℝ) ≤ Fintype.card State * Fintype.card Action)
    linarith
  -- sample-size hypothesis
  set mx := max (Real.sqrt σ) σ
  have hmx1 : Real.sqrt σ ≤ mx := le_max_left _ _
  have hmx2 : σ ≤ mx := le_max_right _ _
  have hmx0 : 0 ≤ mx := le_trans (Real.sqrt_nonneg σ) hmx1
  have hsampleC : (10 ^ 6 + 8 * c_opt) * (1 + mx / (1 - M.discount)) *
      Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤
      N * ((1 - M.discount) ^ 3 * ε ^ 2) := by
    have hden : 0 < (1 - M.discount) ^ 3 * ε ^ 2 := by positivity
    have e : (10 ^ 6 + 8 * c_opt) / ((1 - M.discount) ^ 3 * ε ^ 2) *
        (1 + mx / (1 - M.discount)) *
        Real.log (Fintype.card State * Fintype.card Action * N / δ) =
        (10 ^ 6 + 8 * c_opt) * (1 + mx / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) := by ring
    rw [e, div_le_iff₀ hden] at hsample
    exact hsample
  have hsample' : 10 ^ 6 * (1 + mx / (1 - M.discount)) *
      Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤
      N * ((1 - M.discount) ^ 3 * ε ^ 2) := by
    have h0 : 0 ≤ (1 + mx / (1 - M.discount)) *
        Real.log (Fintype.card State * Fintype.card Action * N / δ) := by
      have : 0 ≤ mx / (1 - M.discount) := by positivity
      exact mul_nonneg (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_right (show (10 : ℝ) ^ 6 ≤ 10 ^ 6 + 8 * c_opt by linarith) h0
    rw [← mul_assoc, ← mul_assoc] at this
    linarith
  -- ℓ ≤ N
  have hℓN : ℓ ≤ N := by
    have hεg' : ε * (1 - M.discount) ≤ 1 := by rw [le_div_iff₀ hg] at hεg; linarith
    have hsmall : (1 - M.discount) ^ 3 * ε ^ 2 ≤ 1 := by
      have h1 : (ε * (1 - M.discount)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hεg'
      have h2 : 1 - M.discount ≤ 1 := by linarith
      have e : (1 - M.discount) ^ 3 * ε ^ 2 = (1 - M.discount) * (ε * (1 - M.discount)) ^ 2 := by
        ring
      rw [e]
      calc (1 - M.discount) * (ε * (1 - M.discount)) ^ 2 ≤ 1 * 1 :=
            mul_le_mul h2 h1 (by positivity) zero_le_one
        _ = 1 := by ring
    have h1 : 10 ^ 6 * Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N := by
      have hL0 : 0 ≤ Real.log (Fintype.card State * Fintype.card Action * N / δ) := by linarith
      have : 10 ^ 6 * Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤
          10 ^ 6 * (1 + mx / (1 - M.discount)) *
            Real.log (Fintype.card State * Fintype.card Action * N / δ) := by
        have : 0 ≤ mx / (1 - M.discount) := by positivity
        have h5 : 0 ≤ mx / (1 - M.discount) *
            Real.log (Fintype.card State * Fintype.card Action * N / δ) := mul_nonneg this hL0
        linarith
      have h3 : N * ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N :=
        (mul_le_mul_of_nonneg_left hsmall hNR.le).trans (by rw [mul_one])
      linarith
    linarith
  -- planning error of the oracle requirement
  have hSAN : 0 < (Fintype.card State : ℝ) * Fintype.card Action * N := by
    have : (0 : ℝ) < Fintype.card State * Fintype.card Action := by linarith
    positivity
  have hLshift := chi_log_shift hSAN hδ0 hg
  obtain ⟨hΞ1, hplan⟩ := chi_oracle_planning_bounds hγ hγ1 hε0 hεg hN1 hmx0 hc
    (show 8 * c_opt ≤ 10 ^ 6 + 8 * c_opt by linarith) hL hLshift hsampleC
  refine le_of_lt (hprob.trans_le (measureReal_mono ?_ (measure_ne_top _ _)))
  intro data hdata f hf s
  have hΞ0 : 0 ≤ c_opt / (N : ℝ) ^ 2 *
      Real.log (Fintype.card State * Fintype.card Action * N / ((1 - M.discount) * δ)) :=
    (abs_nonneg _).trans (hf s)
  have hnum := chi_selfBoundExpr_le_of_planning hγ hγ1 hσ0 hmx1 hmx2 hε0 hεg hL hℓ0 hℓ hN1
    hsample' hΞ0 hΞ1 hplan
  have hgap := chi_good_gap_of_valueGap M hσ0 hγpos N hN data hℓ0 hℓN hdata f
    (fun t ↦ (le_abs_self _).trans (hf t)) s
  exact hgap.trans hnum

end StatisticalRL.RobustRL.DRVI
