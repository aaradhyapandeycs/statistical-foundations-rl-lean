import Formalization.RobustRL.DRVI.WorstKernel

/-!
# Span of TV-robust values (milestone 2, module S; plan §3.2)

For every stationary policy `π` and TV radius `σ ∈ [0,1]`, the robust value `W = policyFix`
of the TV ball family (true or empirical nominal kernel) satisfies
`max W − min W ≤ 1/(1−γ+γσ)`, and for `γ ≥ 1/4`, `1/(1−γ+γσ) ≤ 4/max{1−γ,σ}`.
The proof moves mass `σ` to the minimizing state: `q = (1−σ)p + σδ_{argmin W} ∈ U(p)`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

section Mix

open Classical

/-- The mixture `(1−σ)p + σδ_x`. -/
noncomputable def tvMix (p : FiniteDistribution State) (x : State) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) : FiniteDistribution State where
  prob y := (1 - σ) * p.prob y + σ * (if y = x then 1 else 0)
  prob_nonneg y := by
    have := p.prob_nonneg y
    split_ifs <;> nlinarith
  sum_prob := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.sum_prob]
    simp

theorem tvMix_expectation (p : FiniteDistribution State) (x : State) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (W : State → ℝ) :
    (tvMix p x hσ0 hσ1).expectation W = (1 - σ) * p.expectation W + σ * W x := by
  simp only [FiniteDistribution.expectation, tvMix, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  congr 1
  simp

theorem tvMix_mem (p : FiniteDistribution State) (x : State) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) : tvMix p x hσ0 hσ1 ∈ tvBall p σ := by
  show (1 / 2 : ℝ) * ∑ y, |p.prob y - (tvMix p x hσ0 hσ1).prob y| ≤ σ
  have hterm : ∀ y, |p.prob y - (tvMix p x hσ0 hσ1).prob y| ≤
      σ * (p.prob y + (if y = x then 1 else 0)) := by
    intro y
    have hp := p.prob_nonneg y
    simp only [tvMix]
    have : p.prob y - ((1 - σ) * p.prob y + σ * (if y = x then 1 else 0)) =
        σ * (p.prob y - (if y = x then 1 else 0)) := by ring
    rw [this, abs_mul, abs_of_nonneg hσ0]
    apply mul_le_mul_of_nonneg_left _ hσ0
    split_ifs
    · rw [abs_le]; constructor <;> linarith
    · rw [sub_zero, abs_of_nonneg hp]; linarith
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) ↦ hterm y)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, p.sum_prob] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  linarith

end Mix

/-- Robust TV values have span at most `1/(1−γ+γσ)` (plan §3.2). -/
theorem tv_policyFix_span (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (π : StationaryPolicy State Action) (s t : State) :
    policyFix (ballFamily tvBall M σ) M π s - policyFix (ballFamily tvBall M σ) M π t ≤
      1 / (1 - M.discount + M.discount * σ) := by
  haveI := M.state_nonempty
  set U := ballFamily tvBall M σ
  set W := policyFix U M π
  have hne : ∀ s a, (U s a).Nonempty := fun s a ↦ ⟨_, tvBall_self_mem (M.transition s a) hσ0⟩
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  obtain ⟨xm, -, hxm⟩ := Finset.exists_min_image Finset.univ W Finset.univ_nonempty
  obtain ⟨xM, -, hxM⟩ := Finset.exists_max_image Finset.univ W Finset.univ_nonempty
  have hm0 : 0 ≤ W xm := (policyFix_bounds U hne M π xm).1
  -- one step of the robust equation at the maximizing state
  have hstep : W xM ≤ 1 + M.discount * ((1 - σ) * W xM + σ * W xm) := by
    have hfix : policyOp U M π W xM = W xM := congrFun (policyFix_spec U M π) xM
    refine (le_of_eq hfix.symm).trans ?_
    unfold policyOp
    apply (π xM).expectation_le_const
    intro a
    have hq := rowInf_le (tvMix_mem (M.transition xM a) xm hσ0 hσ1) W
    rw [tvMix_expectation] at hq
    have hE : (M.transition xM a).expectation W ≤ W xM :=
      (M.transition xM a).expectation_le_const (fun x ↦ hxM x (Finset.mem_univ x))
    have hr := M.reward_le_one xM a
    have h1 : rowInf (U xM a) W ≤ (1 - σ) * W xM + σ * W xm := by
      have : (1 - σ) * (M.transition xM a).expectation W ≤ (1 - σ) * W xM :=
        mul_le_mul_of_nonneg_left hE (by linarith)
      exact hq.trans (by linarith)
    nlinarith
  have hden : 0 < 1 - M.discount + M.discount * σ := by nlinarith
  have hspan : (W xM - W xm) * (1 - M.discount + M.discount * σ) ≤ 1 := by nlinarith
  have hst : W s - W t ≤ W xM - W xm := by
    linarith [hxM s (Finset.mem_univ s), hxm t (Finset.mem_univ t)]
  calc W s - W t ≤ W xM - W xm := hst
    _ ≤ 1 / (1 - M.discount + M.discount * σ) := by
      rw [le_div_iff₀ hden]; exact hspan

theorem tv_optFix_span (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (s t : State) :
    optFix (ballFamily tvBall M σ) M s - optFix (ballFamily tvBall M σ) M t ≤
      1 / (1 - M.discount + M.discount * σ) := by
  rw [← policyFix_optPolicy]
  exact tv_policyFix_span M hσ0 hσ1 _ s t

/-- For `γ ≥ 1/4`: `1/(1−γ+γσ) ≤ 4/max{1−γ,σ}`. -/
theorem tv_span_constant {γ σ : ℝ} (hγ : 1 / 4 ≤ γ) (hγ1 : γ < 1) (hσ0 : 0 ≤ σ) :
    1 / (1 - γ + γ * σ) ≤ 4 / max (1 - γ) σ := by
  have hpos : 0 < 1 - γ := by linarith
  have hmax : 0 < max (1 - γ) σ := lt_max_of_lt_left hpos
  have hden : 0 < 1 - γ + γ * σ := by nlinarith
  rw [div_le_div_iff₀ hden hmax]
  rcases le_total (1 - γ) σ with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

end StatisticalRL.RobustRL.DRVI
