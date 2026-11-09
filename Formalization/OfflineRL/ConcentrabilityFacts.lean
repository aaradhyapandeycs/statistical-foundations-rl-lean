import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.OptimalTrajectoryValue
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Elementary facts on concentrability coefficients

Source: `chapters/offlineRL.tex:128–185` (Definition 6.1, Remarks 6.2 and 6.3) and `:264–281`
(`eq:defn-Cstar-bandits`). Ratios are taken in `ℝ≥0∞`, so `0/0 = 0` (the source convention) and
`x/0 = ∞` for `x > 0`.

* `one_le_iSup_ratio`: for probability vectors `p, q` on a finite type, `max p/q ≥ 1`.
* `ofReal_le_iSup_clipped_ratio`: for `0 ≤ c ≤ 1`, `max min{p, c}/q ≥ c`.
* `iSup_clipped_ratio_le`: clipping does not increase the coefficient.
* `discountedJointOccupancy` specializations: `cstar_ge_one`, `cstarClipped_le_cstar`,
  `cstarClipped_ge_inv_card`, and the attaining instance `exists_cstarClipped_eq_inv_card`.
* `iSup_pointMass_ratio`: the bandit identity `max_a 1{a = a⋆}/d^b(a) = 1/d^b(a⋆)`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.OfflineRL.Concentrability

/-- `max_x p(x)/q(x) ≥ 1` for probability vectors on a finite type (`ℝ≥0∞` ratios). -/
theorem one_le_iSup_ratio {X : Type*} [Fintype X] (p q : FiniteDistribution X) :
    1 ≤ ⨆ x, ENNReal.ofReal (p.prob x) / ENNReal.ofReal (q.prob x) := by
  by_contra h
  push_neg at h
  have hx : ∀ x, ENNReal.ofReal (p.prob x) / ENNReal.ofReal (q.prob x) < 1 :=
    fun x ↦ lt_of_le_of_lt (le_iSup (fun x ↦ ENNReal.ofReal (p.prob x) /
      ENNReal.ofReal (q.prob x)) x) h
  have hle : ∀ x, p.prob x ≤ q.prob x := by
    intro x
    rcases (p.prob_nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; exact q.prob_nonneg x
    · have hne : ENNReal.ofReal (p.prob x) ≠ 0 := by
        simpa [ENNReal.ofReal_eq_zero, not_le] using hpos
      have := (ENNReal.div_lt_iff (Or.inr hne) (Or.inr ENNReal.ofReal_ne_top)).1 (hx x)
      rw [one_mul, ENNReal.ofReal_lt_ofReal_iff'] at this
      exact this.1.le
  have hlt : ∃ x ∈ (Finset.univ : Finset X), p.prob x < q.prob x := by
    have : ∃ x, 0 < p.prob x := by
      by_contra hall
      push_neg at hall
      have := Finset.sum_nonpos (s := Finset.univ) (fun x _ ↦ hall x)
      linarith [p.sum_prob]
    obtain ⟨x, hpos⟩ := this
    refine ⟨x, Finset.mem_univ x, ?_⟩
    have hne : ENNReal.ofReal (p.prob x) ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero, not_le] using hpos
    have := (ENNReal.div_lt_iff (Or.inr hne) (Or.inr ENNReal.ofReal_ne_top)).1 (hx x)
    rw [one_mul, ENNReal.ofReal_lt_ofReal_iff'] at this
    exact this.1
  have := Finset.sum_lt_sum (fun x _ ↦ hle x) hlt
  rw [p.sum_prob, q.sum_prob] at this
  exact lt_irrefl _ this

/-- Clipping the numerator does not increase the coefficient. -/
theorem iSup_clipped_ratio_le {X : Type*} (p q : X → ℝ) (c : ℝ) :
    (⨆ x, ENNReal.ofReal (min (p x) c) / ENNReal.ofReal (q x)) ≤
      ⨆ x, ENNReal.ofReal (p x) / ENNReal.ofReal (q x) :=
  iSup_mono fun _ ↦ ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (min_le_left _ _)) _

/-- For `c ≤ 1`, the clipped coefficient `max min{p, c}/q` is at least `c`. -/
theorem ofReal_le_iSup_clipped_ratio {X : Type*} [Fintype X] (p q : FiniteDistribution X)
    {c : ℝ} (hc1 : c ≤ 1) :
    ENNReal.ofReal c ≤ ⨆ x, ENNReal.ofReal (min (p.prob x) c) / ENNReal.ofReal (q.prob x) := by
  by_cases h : ∃ x, c ≤ p.prob x
  · obtain ⟨x, hx⟩ := h
    refine le_trans ?_ (le_iSup (fun x ↦ ENNReal.ofReal (min (p.prob x) c) /
      ENNReal.ofReal (q.prob x)) x)
    rw [min_eq_right hx]
    rcases eq_or_ne (ENNReal.ofReal c) 0 with h0 | h0
    · rw [h0]; exact zero_le _
    rw [ENNReal.le_div_iff_mul_le (Or.inr h0) (Or.inl ENNReal.ofReal_ne_top)]
    refine mul_le_of_le_one_right' ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (StatisticalRL.DiscountedMDP.finiteDistribution_prob_le_one q x)
  · push_neg at h
    have heq : (fun x ↦ ENNReal.ofReal (min (p.prob x) c) / ENNReal.ofReal (q.prob x)) =
        fun x ↦ ENNReal.ofReal (p.prob x) / ENNReal.ofReal (q.prob x) := by
      funext x; rw [min_eq_left (h x).le]
    rw [heq]
    calc ENNReal.ofReal c ≤ 1 := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc1
      _ ≤ _ := one_le_iSup_ratio p q

/-- The bandit form of the coefficient: `max_b 1{b = a⋆}/d(b) = 1/d(a⋆)` in `ℝ≥0∞`. -/
theorem iSup_pointMass_ratio {Arm : Type*} [DecidableEq Arm] [MeasurableSpace Arm]
    (d : Measure Arm) (aStar : Arm) :
    (⨆ b : Arm, (if b = aStar then (1 : ℝ≥0∞) else 0) / d {b}) = (d {aStar})⁻¹ := by
  apply le_antisymm
  · refine iSup_le fun b ↦ ?_
    by_cases hb : b = aStar
    · subst hb; simp
    · simp [hb]
  · refine le_trans ?_ (le_iSup (fun b : Arm ↦ (if b = aStar then (1 : ℝ≥0∞) else 0) / d {b})
      aStar)
    simp

end StatisticalRL.OfflineRL.Concentrability

namespace StatisticalRL.DiscountedMDP

open StatisticalRL.OfflineRL.Concentrability

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Remark 6.2: `C⋆ ≥ 1` for the discounted joint occupancy of every stationary policy. -/
theorem cstar_ge_one (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (db : FiniteDistribution (State × Action)) :
    1 ≤ ⨆ sa : State × Action,
      ENNReal.ofReal (M.discountedJointOccupancy π ρ sa.1 sa.2) / ENNReal.ofReal (db.prob sa) :=
  one_le_iSup_ratio (M.discountedJointLaw π ρ) db

/-- Remark 6.3 (i): the clipped coefficient is at most `C⋆`. -/
theorem cstarClipped_le_cstar (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : FiniteDistribution State) (db : FiniteDistribution (State × Action)) :
    (⨆ sa : State × Action, ENNReal.ofReal (min (M.discountedJointOccupancy π ρ sa.1 sa.2)
        (1 / (Fintype.card State : ℝ))) / ENNReal.ofReal (db.prob sa)) ≤
      ⨆ sa : State × Action, ENNReal.ofReal (M.discountedJointOccupancy π ρ sa.1 sa.2) /
        ENNReal.ofReal (db.prob sa) :=
  iSup_clipped_ratio_le (fun sa : State × Action ↦ M.discountedJointOccupancy π ρ sa.1 sa.2)
    db.prob _

/-- Remark 6.3 (iii): the clipped coefficient is at least `1/S`. -/
theorem cstarClipped_ge_inv_card (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (ρ : FiniteDistribution State)
    (db : FiniteDistribution (State × Action)) :
    ENNReal.ofReal (1 / (Fintype.card State : ℝ)) ≤
      ⨆ sa : State × Action, ENNReal.ofReal (min (M.discountedJointOccupancy π ρ sa.1 sa.2)
        (1 / (Fintype.card State : ℝ))) / ENNReal.ofReal (db.prob sa) := by
  haveI := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hc : 1 / (Fintype.card State : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hS
  exact ofReal_le_iSup_clipped_ratio (M.discountedJointLaw π ρ) db hc

private theorem pointMass_prob_eq {α : Type*} [Fintype α] [DecidableEq α] (x y : α) :
    (EnvironmentStage.pointMass x).prob y = if y = x then 1 else 0 := by
  unfold EnvironmentStage.pointMass
  by_cases h : y = x <;> simp [h]

/-- The discount-zero instance used for Remark 6.3 (ii): all transitions go to `s₀`, zero
reward, discount `0`. -/
noncomputable def clippedWitnessMDP (State Action : Type*) [Fintype State] [Fintype Action]
    [Nonempty State] [Nonempty Action] (s₀ : State) : DiscountedMDP State Action where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition _ _ := EnvironmentStage.pointMass s₀
  reward _ _ := 0
  reward_nonneg _ _ := le_rfl
  reward_le_one _ _ := zero_le_one
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-- Remark 6.3 (ii): the clipped coefficient of the optimal deterministic policy can equal
`1/S`. Take discount `0`, `ρ = δ_{s₀}` and `d^b = δ_{(s₀, π⋆(s₀))}`. -/
theorem exists_cstarClipped_eq_inv_card (State Action : Type*) [Fintype State] [Fintype Action]
    [Nonempty State] [Nonempty Action] :
    ∃ (M : DiscountedMDP State Action) (ρ : FiniteDistribution State)
      (db : FiniteDistribution (State × Action)),
      (⨆ sa : State × Action, ENNReal.ofReal (min
          (M.discountedJointOccupancy M.optimalGreedyPolicy ρ sa.1 sa.2)
          (1 / (Fintype.card State : ℝ))) / ENNReal.ofReal (db.prob sa)) =
        ENNReal.ofReal (1 / (Fintype.card State : ℝ)) := by
  classical
  let s₀ : State := Classical.arbitrary State
  let M := clippedWitnessMDP State Action s₀
  let g := M.optimalGreedyAction s₀
  refine ⟨M, EnvironmentStage.pointMass s₀, EnvironmentStage.pointMass (s₀, g), ?_⟩
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hc : 1 / (Fintype.card State : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hS
  have hocc : ∀ s a, M.discountedJointOccupancy M.optimalGreedyPolicy
      (EnvironmentStage.pointMass s₀) s a = if (s, a) = (s₀, g) then 1 else 0 := by
    intro s a
    rw [M.discountedJointOccupancy_discount_zero _ _ s a rfl]
    simp only [optimalGreedyPolicy, pointMass_prob_eq, Prod.mk.injEq]
    by_cases hs : s = s₀
    · subst hs; by_cases ha : a = g <;> simp [ha, g]
    · simp [hs]
  apply le_antisymm
  · refine iSup_le fun sa ↦ ?_
    rw [hocc sa.1 sa.2, pointMass_prob_eq]
    by_cases h : sa = (s₀, g)
    · simp only [h, if_true, ENNReal.ofReal_one, div_one]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · simp only [Prod.mk.eta, h, if_false]
      rw [min_eq_left (by positivity)]
      simp
  · refine le_trans ?_ (le_iSup (fun sa : State × Action ↦ ENNReal.ofReal (min
      (M.discountedJointOccupancy M.optimalGreedyPolicy (EnvironmentStage.pointMass s₀) sa.1 sa.2)
      (1 / (Fintype.card State : ℝ))) / ENNReal.ofReal
        ((EnvironmentStage.pointMass (s₀, g)).prob sa)) (s₀, g))
    rw [hocc, pointMass_prob_eq]
    simp only [if_true, ENNReal.ofReal_one, div_one]
    rw [min_eq_right hc]

end StatisticalRL.DiscountedMDP
