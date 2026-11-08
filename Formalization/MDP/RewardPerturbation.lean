import Formalization.MDP.FixedPoint
import Formalization.MDP.OptimalTrajectoryValue

/-!
# Reward perturbation bounds for discounted MDPs

Source: arXiv:2610.41903v1, `chapters/prelim.tex:613–653`, equations
`eq:QV-pi-perturbabtion-r-inf` (2.27) and `eq:QV-star-perturbabtion-r-inf` (2.28).
Two discounted MDPs share the transition kernel and the discount and differ only in the
reward. The policy and optimal Bellman solutions move by at most `‖r − r̃‖∞/(1−γ)`.
The proof is the Bellman self-bound `D ≤ ‖r − r̃‖∞ + γ D`, not the printed resolvent route.
-/

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A coordinate of a two-argument real function is bounded by its sup norm. -/
theorem abs_apply₂_le_norm (f : State → Action → ℝ) (s : State) (a : Action) :
    |f s a| ≤ ‖f‖ := by
  have h1 : ‖f s a‖ ≤ ‖f s‖ := norm_le_pi_norm (f s) a
  have h2 : ‖f s‖ ≤ ‖f‖ := norm_le_pi_norm f s
  rw [← Real.norm_eq_abs]
  exact h1.trans h2

/-- Sup norm of a two-argument real function from a pointwise bound. -/
theorem norm_le_of_abs_apply₂_le {f : State → Action → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s a, |f s a| ≤ c) : ‖f‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun s ↦
    (pi_norm_le_iff_of_nonneg hc).2 fun a ↦ by
      rw [Real.norm_eq_abs]
      exact h s a

/-- Sup norm of a one-argument real function from a pointwise bound. -/
theorem norm_le_of_abs_apply_le {f : State → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s, |f s| ≤ c) : ‖f‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun s ↦ by
    rw [Real.norm_eq_abs]
    exact h s

/-- eq. (2.27), Q part: with a common kernel and discount,
`‖Q^π − Q̃^π‖∞ ≤ ‖r − r̃‖∞/(1−γ)` for every stationary randomized policy. -/
theorem policyFixedPoint_sub_norm_le_of_reward (M M' : DiscountedMDP State Action)
    (hP : M'.transition = M.transition) (hγ : M'.discount = M.discount)
    (π : StationaryPolicy State Action) :
    ‖M.policyFixedPoint π - M'.policyFixedPoint π‖ ≤
      ‖M.reward - M'.reward‖ / (1 - M.discount) := by
  set Q := M.policyFixedPoint π with hQdef
  set Q' := M'.policyFixedPoint π with hQ'def
  set d := ‖M.reward - M'.reward‖
  set D := ‖Q - Q'‖
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hpt : ∀ t b, |Q t b - Q' t b| ≤ D := fun t b ↦ by
    simpa only [Pi.sub_apply] using abs_apply₂_le_norm (Q - Q') t b
  have hr : ∀ s a, |M.reward s a - M'.reward s a| ≤ d := fun s a ↦ by
    simpa only [Pi.sub_apply] using abs_apply₂_le_norm (M.reward - M'.reward) s a
  have key : ∀ s a, |Q s a - Q' s a| ≤ d + M.discount * D := by
    intro s a
    have hQ : M.qBellman π Q s a = Q s a :=
      congrFun (congrFun (M.policyFixedPoint_spec π) s) a
    have hQ' : M'.qBellman π Q' s a = Q' s a :=
      congrFun (congrFun (M'.policyFixedPoint_spec π) s) a
    have e : Q s a - Q' s a = (M.reward s a - M'.reward s a) + M.discount *
        ((M.transition s a).expectation (fun t ↦ (π t).expectation (Q t)) -
          (M.transition s a).expectation (fun t ↦ (π t).expectation (Q' t))) := by
      rw [← hQ, ← hQ']
      simp only [qBellman, hP, hγ]
      ring
    have hinner : |(M.transition s a).expectation (fun t ↦ (π t).expectation (Q t)) -
        (M.transition s a).expectation (fun t ↦ (π t).expectation (Q' t))| ≤ D :=
      (M.transition s a).abs_expectation_sub_le
        (fun t ↦ (π t).abs_expectation_sub_le (fun b ↦ hpt t b))
    rw [e]
    calc
      _ ≤ |M.reward s a - M'.reward s a| + |M.discount *
          ((M.transition s a).expectation (fun t ↦ (π t).expectation (Q t)) -
            (M.transition s a).expectation (fun t ↦ (π t).expectation (Q' t)))| :=
        abs_add_le _ _
      _ ≤ d + M.discount * D := by
        rw [abs_mul, abs_of_nonneg hγ0]
        exact add_le_add (hr s a) (mul_le_mul_of_nonneg_left hinner hγ0)
  have hd0 : 0 ≤ d := norm_nonneg _
  have hD0 : 0 ≤ D := norm_nonneg _
  have hself : D ≤ d + M.discount * D :=
    norm_le_of_abs_apply₂_le (by positivity) (fun s a ↦ by
      simpa only [Pi.sub_apply] using key s a)
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- eq. (2.27), V part: `‖V^π − Ṽ^π‖∞ ≤ ‖r − r̃‖∞/(1−γ)` with `V^π(s) = E_{a∼π(s)} Q^π(s,a)`. -/
theorem policyValue_sub_norm_le_of_reward (M M' : DiscountedMDP State Action)
    (hP : M'.transition = M.transition) (hγ : M'.discount = M.discount)
    (π : StationaryPolicy State Action) :
    ‖(fun s ↦ (π s).expectation (M.policyFixedPoint π s)) -
        (fun s ↦ (π s).expectation (M'.policyFixedPoint π s))‖ ≤
      ‖M.reward - M'.reward‖ / (1 - M.discount) := by
  have hQ := M.policyFixedPoint_sub_norm_le_of_reward M' hP hγ π
  have hc : 0 ≤ ‖M.reward - M'.reward‖ / (1 - M.discount) :=
    div_nonneg (norm_nonneg _) (by linarith [M.discount_lt_one])
  refine norm_le_of_abs_apply_le hc (fun s ↦ ?_)
  simp only [Pi.sub_apply]
  refine (π s).abs_expectation_sub_le (fun b ↦ ?_)
  have := abs_apply₂_le_norm (M.policyFixedPoint π - M'.policyFixedPoint π) s b
  simp only [Pi.sub_apply] at this
  linarith

/-- Two bounded-above real families with uniformly close entries have close suprema. -/
theorem abs_ciSup_sub_ciSup_le {ι : Sort*} [Nonempty ι] {f g : ι → ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) {c : ℝ}
    (h : ∀ i, |f i - g i| ≤ c) : |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  have h1 : (⨆ i, f i) ≤ (⨆ i, g i) + c := ciSup_le fun i ↦ by
    have := (abs_le.mp (h i)).2
    have := le_ciSup hg i
    linarith
  have h2 : (⨆ i, g i) ≤ (⨆ i, f i) + c := ciSup_le fun i ↦ by
    have := (abs_le.mp (h i)).1
    have := le_ciSup hf i
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The pointwise supremum of the policy Bellman solutions over stationary randomized
policies is the optimality Bellman solution (attained by `optimalGreedyPolicy`). -/
theorem iSup_policyFixedPoint_eq_optimalityFixedPoint (M : DiscountedMDP State Action) :
    (fun s a ↦ ⨆ π : StationaryPolicy State Action, M.policyFixedPoint π s a) =
      M.optimalityFixedPoint := by
  haveI : Nonempty (StationaryPolicy State Action) := ⟨M.optimalGreedyPolicy⟩
  funext s a
  apply le_antisymm
  · exact ciSup_le fun π ↦ M.policyFixedPoint_le_optimal π s a
  · refine le_ciSup_of_le ⟨M.optimalityFixedPoint s a, ?_⟩ M.optimalGreedyPolicy ?_
    · rintro _ ⟨π, rfl⟩
      exact M.policyFixedPoint_le_optimal π s a
    · rw [M.policyFixedPoint_optimalGreedy]

/-- The state values of all stationary randomized policies are bounded above by `1/(1−γ)`. -/
theorem bddAbove_policyValue (M : DiscountedMDP State Action) (s : State) :
    BddAbove (Set.range fun π : StationaryPolicy State Action ↦
      (π s).expectation (M.policyFixedPoint π s)) := by
  refine ⟨1 / (1 - M.discount), ?_⟩
  rintro _ ⟨π, rfl⟩
  exact (π s).expectation_le_const (fun b ↦ (M.policyFixedPoint_bounds π s b).2)

/-- eq. (2.28): the full printed chain for `Q⋆` and the `V⋆` bound, with `max_π` read as the
supremum over stationary randomized policies. -/
theorem optimal_reward_perturbation (M M' : DiscountedMDP State Action)
    (hP : M'.transition = M.transition) (hγ : M'.discount = M.discount) :
    ((fun s a ↦ ⨆ π : StationaryPolicy State Action, M.policyFixedPoint π s a) =
        M.optimalityFixedPoint ∧
      (fun s a ↦ ⨆ π : StationaryPolicy State Action, M'.policyFixedPoint π s a) =
        M'.optimalityFixedPoint) ∧
    ‖(fun s a ↦ ⨆ π : StationaryPolicy State Action, M.policyFixedPoint π s a) -
        (fun s a ↦ ⨆ π : StationaryPolicy State Action, M'.policyFixedPoint π s a)‖ ≤
      (⨆ π : StationaryPolicy State Action,
        ‖M.policyFixedPoint π - M'.policyFixedPoint π‖) ∧
    (⨆ π : StationaryPolicy State Action,
        ‖M.policyFixedPoint π - M'.policyFixedPoint π‖) ≤
      ‖M.reward - M'.reward‖ / (1 - M.discount) ∧
    ‖(fun s ↦ ⨆ π : StationaryPolicy State Action,
          (π s).expectation (M.policyFixedPoint π s)) -
        (fun s ↦ ⨆ π : StationaryPolicy State Action,
          (π s).expectation (M'.policyFixedPoint π s))‖ ≤
      ‖M.reward - M'.reward‖ / (1 - M.discount) := by
  haveI : Nonempty (StationaryPolicy State Action) := ⟨M.optimalGreedyPolicy⟩
  set c := ‖M.reward - M'.reward‖ / (1 - M.discount)
  have hc : 0 ≤ c := div_nonneg (norm_nonneg _) (by linarith [M.discount_lt_one])
  have hπ : ∀ π, ‖M.policyFixedPoint π - M'.policyFixedPoint π‖ ≤ c :=
    M.policyFixedPoint_sub_norm_le_of_reward M' hP hγ
  have hbddN : BddAbove (Set.range fun π : StationaryPolicy State Action ↦
      ‖M.policyFixedPoint π - M'.policyFixedPoint π‖) := ⟨c, by rintro _ ⟨π, rfl⟩; exact hπ π⟩
  have hbddQ : ∀ (N : DiscountedMDP State Action) s a,
      BddAbove (Set.range fun π : StationaryPolicy State Action ↦ N.policyFixedPoint π s a) :=
    fun N s a ↦ ⟨1 / (1 - N.discount), by
      rintro _ ⟨π, rfl⟩; exact (N.policyFixedPoint_bounds π s a).2⟩
  have hsupN0 : 0 ≤ ⨆ π : StationaryPolicy State Action,
      ‖M.policyFixedPoint π - M'.policyFixedPoint π‖ :=
    (norm_nonneg _).trans (le_ciSup hbddN M.optimalGreedyPolicy)
  refine ⟨⟨M.iSup_policyFixedPoint_eq_optimalityFixedPoint,
    M'.iSup_policyFixedPoint_eq_optimalityFixedPoint⟩, ?_, ciSup_le hπ, ?_⟩
  · refine norm_le_of_abs_apply₂_le hsupN0 (fun s a ↦ ?_)
    simp only [Pi.sub_apply]
    refine abs_ciSup_sub_ciSup_le (hbddQ M s a) (hbddQ M' s a) (fun π ↦ ?_)
    have := abs_apply₂_le_norm (M.policyFixedPoint π - M'.policyFixedPoint π) s a
    simp only [Pi.sub_apply] at this
    exact this.trans (le_ciSup hbddN π)
  · refine norm_le_of_abs_apply_le hc (fun s ↦ ?_)
    simp only [Pi.sub_apply]
    refine abs_ciSup_sub_ciSup_le (M.bddAbove_policyValue s) (M'.bddAbove_policyValue s)
      (fun π ↦ ?_)
    have := M.policyValue_sub_norm_le_of_reward M' hP hγ π
    have h2 := norm_le_pi_norm ((fun s ↦ (π s).expectation (M.policyFixedPoint π s)) -
        (fun s ↦ (π s).expectation (M'.policyFixedPoint π s))) s
    rw [Real.norm_eq_abs, Pi.sub_apply] at h2
    exact h2.trans this

end StatisticalRL.DiscountedMDP
