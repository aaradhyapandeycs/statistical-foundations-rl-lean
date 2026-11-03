import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite tabular MDPs and policy Bellman operators

The probability simplex, discounted model, and randomized stationary policy below
transcribe Chapter 2, Section 2.1 of arXiv:2610.41903v1. Expectations are actual
finite weighted sums. No value function is defined by assuming a Bellman equation:
the link to the paper's expected infinite trajectory return is a separate task.
-/

open scoped BigOperators

namespace StatisticalRL

/-- The real probability simplex on a finite carrier. -/
structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  sum_prob : ∑ x, prob x = 1

namespace FiniteDistribution

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- Expectation under an actual finite probability vector. -/
def expectation (d : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, d.prob x * f x

@[simp]
theorem expectation_const (d : FiniteDistribution Ω) (c : ℝ) :
    d.expectation (fun _ ↦ c) = c := by
  rw [expectation, ← Finset.sum_mul, d.sum_prob, one_mul]

theorem expectation_add (d : FiniteDistribution Ω) (f g : Ω → ℝ) :
    d.expectation (fun x ↦ f x + g x) = d.expectation f + d.expectation g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (d : FiniteDistribution Ω) (f g : Ω → ℝ) :
    d.expectation (fun x ↦ f x - g x) = d.expectation f - d.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul (d : FiniteDistribution Ω) (c : ℝ) (f : Ω → ℝ) :
    d.expectation (fun x ↦ c * f x) = c * d.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_mono (d : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x ≤ g x) : d.expectation f ≤ d.expectation g := by
  exact Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (d.prob_nonneg x)

theorem expectation_nonneg (d : FiniteDistribution Ω) {f : Ω → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ d.expectation f := by
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (d.prob_nonneg x) (h x)

theorem expectation_le_const (d : FiniteDistribution Ω) {f : Ω → ℝ} {c : ℝ}
    (h : ∀ x, f x ≤ c) : d.expectation f ≤ c := by
  calc
    d.expectation f ≤ d.expectation (fun _ ↦ c) := d.expectation_mono h
    _ = c := d.expectation_const c

theorem abs_expectation_le (d : FiniteDistribution Ω) {f : Ω → ℝ} {c : ℝ}
    (h : ∀ x, |f x| ≤ c) : |d.expectation f| ≤ c := by
  calc
    |d.expectation f| ≤ ∑ x, |d.prob x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = d.expectation (fun x ↦ |f x|) := by
      simp only [expectation, abs_mul, abs_of_nonneg (d.prob_nonneg _)]
    _ ≤ c := d.expectation_le_const h

theorem abs_expectation_sub_le (d : FiniteDistribution Ω) {f g : Ω → ℝ} {c : ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |d.expectation f - d.expectation g| ≤ c := by
  rw [← d.expectation_sub f g]
  exact d.abs_expectation_le h

/-- Mixture of finite probability vectors; all probability obligations are proved. -/
def bind (d : FiniteDistribution Ω) (k : Ω → FiniteDistribution Ξ) :
    FiniteDistribution Ξ where
  prob y := d.expectation (fun x ↦ (k x).prob y)
  prob_nonneg y := d.expectation_nonneg (fun x ↦ (k x).prob_nonneg y)
  sum_prob := by
    simp only [expectation]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_prob, mul_one]
    exact d.sum_prob

theorem expectation_bind (d : FiniteDistribution Ω) (k : Ω → FiniteDistribution Ξ)
    (f : Ξ → ℝ) :
    (d.bind k).expectation f = d.expectation (fun x ↦ (k x).expectation f) := by
  simp only [expectation, bind]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- A probability vector on a singleton carrier assigns mass one to its only point. -/
theorem prob_eq_one_of_subsingleton [Subsingleton Ω] (d : FiniteDistribution Ω) (x : Ω) :
    d.prob x = 1 := by
  letI : Unique Ω := ⟨⟨x⟩, fun y ↦ Subsingleton.elim y x⟩
  simpa only [Fintype.sum_unique] using d.sum_prob

end FiniteDistribution

/-- The source's stationary discounted model, with its exact reward and discount bounds. -/
structure DiscountedMDP (State Action : Type*) [Fintype State] [Fintype Action] where
  state_nonempty : Nonempty State
  action_nonempty : Nonempty Action
  transition : State → Action → FiniteDistribution State
  reward : State → Action → ℝ
  reward_nonneg : ∀ s a, 0 ≤ reward s a
  reward_le_one : ∀ s a, reward s a ≤ 1
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

/-- A stationary randomized policy assigns a probability vector over actions to each state. -/
abbrev StationaryPolicy (State Action : Type*) [Fintype Action] :=
  State → FiniteDistribution Action

/-- There is only one deterministic policy when the action carrier has one element. -/
theorem deterministic_policy_eq_of_subsingleton {State Action : Type*} [Subsingleton Action]
    (π₁ π₂ : State → Action) : π₁ = π₂ := by
  funext s
  exact Subsingleton.elim (π₁ s) (π₂ s)

/-- The genuine maximum over a nonempty finite action set. -/
noncomputable def actionMaximum {Action : Type*} [Fintype Action] [Nonempty Action]
    (f : Action → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem le_actionMaximum {Action : Type*} [Fintype Action] [Nonempty Action]
    (f : Action → ℝ) (a : Action) : f a ≤ actionMaximum f :=
  Finset.le_sup' f (Finset.mem_univ a)

/-- A finite maximum is nonexpansive for a uniform pointwise perturbation. -/
theorem abs_actionMaximum_sub_le {Action : Type*} [Fintype Action] [Nonempty Action]
    {f g : Action → ℝ} {ε : ℝ} (h : ∀ a, |f a - g a| ≤ ε) :
    |actionMaximum f - actionMaximum g| ≤ ε := by
  have hfg : actionMaximum f ≤ actionMaximum g + ε := by
    apply (Finset.sup'_le_iff Finset.univ_nonempty f).2
    intro a _
    have hpoint := (abs_le.mp (h a)).2
    have hmax := le_actionMaximum g a
    linarith only [hpoint, hmax]
  have hgf : actionMaximum g ≤ actionMaximum f + ε := by
    apply (Finset.sup'_le_iff Finset.univ_nonempty g).2
    intro a _
    have hpoint := (abs_le.mp (h a)).1
    have hmax := le_actionMaximum f a
    linarith only [hpoint, hmax]
  exact abs_le.mpr ⟨by linarith only [hgf], by linarith only [hfg]⟩

namespace DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The policy-induced stochastic transition kernel, equation `eq:defn-P-s-pi-inf`. -/
def policyTransition (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) : FiniteDistribution State :=
  (π s).bind (M.transition s)

@[simp]
theorem policyTransition_prob (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s t : State) :
    (M.policyTransition π s).prob t =
      (π s).expectation (fun a ↦ (M.transition s a).prob t) := rfl

/-- The source's Q-function Bellman consistency operator, `eq:bellman_consistency_operator`. -/
def qBellman (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  M.reward s a + M.discount *
    (M.transition s a).expectation (fun t ↦ (π t).expectation (Q t))

/-- The state-value Bellman consistency operator in `eq:bellman_consistency-V-all`. -/
def valueBellman (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V : State → ℝ) (s : State) : ℝ :=
  (π s).expectation (M.reward s) +
    M.discount * (M.policyTransition π s).expectation V

/-- The source's Bellman optimality operator, `eq:bellman_optimality_operator`. -/
noncomputable def qOptimality (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  letI : Nonempty Action := M.action_nonempty
  M.reward s a + M.discount * (M.transition s a).expectation (fun t ↦ actionMaximum (Q t))

/-- Exact pointwise uniform-modulus form of the policy Q-Bellman contraction bound. -/
theorem abs_qBellman_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {Q₁ Q₂ : State → Action → ℝ} {ε : ℝ}
    (h : ∀ s a, |Q₁ s a - Q₂ s a| ≤ ε) (s : State) (a : Action) :
    |M.qBellman π Q₁ s a - M.qBellman π Q₂ s a| ≤ M.discount * ε := by
  have hinner (t : State) : |(π t).expectation (Q₁ t) - (π t).expectation (Q₂ t)| ≤ ε :=
    (π t).abs_expectation_sub_le (h t)
  have houter := (M.transition s a).abs_expectation_sub_le hinner
  calc
    |M.qBellman π Q₁ s a - M.qBellman π Q₂ s a| = M.discount *
        |(M.transition s a).expectation (fun t ↦ (π t).expectation (Q₁ t)) -
          (M.transition s a).expectation (fun t ↦ (π t).expectation (Q₂ t))| := by
      unfold qBellman
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.discount_nonneg]
    _ ≤ M.discount * ε := mul_le_mul_of_nonneg_left houter M.discount_nonneg

/-- Exact pointwise uniform-modulus contraction for policy state-value evaluation. -/
theorem abs_valueBellman_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {V₁ V₂ : State → ℝ} {ε : ℝ}
    (h : ∀ s, |V₁ s - V₂ s| ≤ ε) (s : State) :
    |M.valueBellman π V₁ s - M.valueBellman π V₂ s| ≤ M.discount * ε := by
  have hnext := (M.policyTransition π s).abs_expectation_sub_le h
  calc
    |M.valueBellman π V₁ s - M.valueBellman π V₂ s| =
        M.discount * |(M.policyTransition π s).expectation V₁ -
          (M.policyTransition π s).expectation V₂| := by
      unfold valueBellman
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.discount_nonneg]
    _ ≤ M.discount * ε := mul_le_mul_of_nonneg_left hnext M.discount_nonneg

/-- Pointwise uniform-modulus contraction for the optimality Bellman operator. -/
theorem abs_qOptimality_sub_le (M : DiscountedMDP State Action)
    {Q₁ Q₂ : State → Action → ℝ} {ε : ℝ}
    (h : ∀ s a, |Q₁ s a - Q₂ s a| ≤ ε) (s : State) (a : Action) :
    |M.qOptimality Q₁ s a - M.qOptimality Q₂ s a| ≤ M.discount * ε := by
  letI : Nonempty Action := M.action_nonempty
  have hnext := (M.transition s a).abs_expectation_sub_le
    (fun t ↦ abs_actionMaximum_sub_le (h t))
  calc
    |M.qOptimality Q₁ s a - M.qOptimality Q₂ s a| = M.discount *
        |(M.transition s a).expectation (fun t ↦ actionMaximum (Q₁ t)) -
          (M.transition s a).expectation (fun t ↦ actionMaximum (Q₂ t))| := by
      unfold qOptimality
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.discount_nonneg]
    _ ≤ M.discount * ε := mul_le_mul_of_nonneg_left hnext M.discount_nonneg

/-- The policy Q-Bellman contraction in the source's finite supremum norm. -/
theorem norm_qBellman_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (Q₁ Q₂ : State → Action → ℝ) :
    ‖M.qBellman π Q₁ - M.qBellman π Q₂‖ ≤ M.discount * ‖Q₁ - Q₂‖ := by
  have hc : 0 ≤ M.discount * ‖Q₁ - Q₂‖ := mul_nonneg M.discount_nonneg (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro a
  rw [Real.norm_eq_abs]
  apply M.abs_qBellman_sub_le π _ s a
  intro t b
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm ((Q₁ - Q₂) t) b).trans (norm_le_pi_norm (Q₁ - Q₂) t)

/-- The policy state-value Bellman contraction in the finite supremum norm. -/
theorem norm_valueBellman_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₁ V₂ : State → ℝ) :
    ‖M.valueBellman π V₁ - M.valueBellman π V₂‖ ≤ M.discount * ‖V₁ - V₂‖ := by
  have hc : 0 ≤ M.discount * ‖V₁ - V₂‖ := mul_nonneg M.discount_nonneg (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  rw [Real.norm_eq_abs]
  apply M.abs_valueBellman_sub_le π _ s
  intro t
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (V₁ - V₂) t

/-- The optimality Q-Bellman contraction in the source's finite supremum norm. -/
theorem norm_qOptimality_sub_le (M : DiscountedMDP State Action)
    (Q₁ Q₂ : State → Action → ℝ) :
    ‖M.qOptimality Q₁ - M.qOptimality Q₂‖ ≤ M.discount * ‖Q₁ - Q₂‖ := by
  have hc : 0 ≤ M.discount * ‖Q₁ - Q₂‖ := mul_nonneg M.discount_nonneg (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro a
  rw [Real.norm_eq_abs]
  apply M.abs_qOptimality_sub_le _ s a
  intro t b
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm ((Q₁ - Q₂) t) b).trans (norm_le_pi_norm (Q₁ - Q₂) t)

/-- The policy Q-Bellman equation has at most one solution, by strict contraction. -/
theorem qBellman_fixedpoint_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {Q₁ Q₂ : State → Action → ℝ}
    (h₁ : M.qBellman π Q₁ = Q₁) (h₂ : M.qBellman π Q₂ = Q₂) : Q₁ = Q₂ := by
  by_contra hne
  have hpos : 0 < ‖Q₁ - Q₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hbound := M.norm_qBellman_sub_le π Q₁ Q₂
  rw [h₁, h₂] at hbound
  exact (not_lt_of_ge hbound) (mul_lt_of_lt_one_left hpos M.discount_lt_one)

/-- The Bellman optimality equation has at most one solution. -/
theorem qOptimality_fixedpoint_unique (M : DiscountedMDP State Action)
    {Q₁ Q₂ : State → Action → ℝ}
    (h₁ : M.qOptimality Q₁ = Q₁) (h₂ : M.qOptimality Q₂ = Q₂) : Q₁ = Q₂ := by
  by_contra hne
  have hpos : 0 < ‖Q₁ - Q₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hbound := M.norm_qOptimality_sub_le Q₁ Q₂
  rw [h₁, h₂] at hbound
  exact (not_lt_of_ge hbound) (mul_lt_of_lt_one_left hpos M.discount_lt_one)

end DiscountedMDP

end StatisticalRL
