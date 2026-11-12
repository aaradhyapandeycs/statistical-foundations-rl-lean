import Formalization.RobustRL.DRVI.DualDeviation
import Formalization.Generative.PolicyLearningLeaveOneOutIndependence

/-!
# Leave-one-out robust absorbing models (milestone 4, module L; plan §3.5)

Robust analogue of the book's state-absorbing models (`generative_model_model_based.tex`,
Lemmas 3.3/3.4). For a state `x` and a level `u`, the absorbing robust model keeps every row set
at states `≠ x`, replaces every row set at `x` by the singleton `{δ_x}` (the *override*: needed for
TV, whose ball around `δ_x` is not a singleton), and pays reward `(1−γ)u` (clamped to `[0,1]`)
at `x`.

* Coincidence: at `u = V(x)` the absorbing fixed point is `V` (optimal and fixed-policy versions).
* Lipschitz in `u`: `|W_u − W_{u'}| ≤ |u − u'|`.
* Off-state factorization: for the empirical ball family, the absorbing family at `x` depends only
  on the samples at states `≠ x`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-! ## Fixed points of nearby operators -/

/-- Two shift-bounded operators that differ by at most `η` have fixed points within
`η/(1−γ)`. -/
theorem fixed_point_dist_le {γ η : ℝ} {T T' : (State → ℝ) → State → ℝ}
    (hT : ShiftBound γ T) (_hγ0 : 0 ≤ γ) (hγ1 : γ < 1) [Nonempty State]
    {F F' : State → ℝ} (hF : T F = F) (hF' : T' F' = F')
    (hη : ∀ V s, |T V s - T' V s| ≤ η) (s : State) :
    |F s - F' s| ≤ η / (1 - γ) := by
  obtain ⟨s₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun t ↦ |F t - F' t|)
    Finset.univ_nonempty
  set m := |F s₀ - F' s₀|
  have hm0 : 0 ≤ m := abs_nonneg _
  have hstep : ∀ t, |F t - F' t| ≤ γ * m + η := by
    intro t
    have h1 := hT.abs_sub_le hm0 (fun x ↦ hmax x (Finset.mem_univ x)) t
    have h2 := hη F' t
    have e : F t - F' t = (T F t - T F' t) + (T F' t - T' F' t) := by
      rw [congrFun hF t, congrFun hF' t]; ring
    rw [e]
    calc |(T F t - T F' t) + (T F' t - T' F' t)| ≤ |T F t - T F' t| + |T F' t - T' F' t| :=
          abs_add_le _ _
      _ ≤ γ * m + η := add_le_add h1 h2
  have hm : m ≤ γ * m + η := hstep s₀
  have hpos : 0 < 1 - γ := by linarith
  have hmη : m ≤ η / (1 - γ) := by
    rw [le_div_iff₀ hpos]; linarith
  exact (hmax s (Finset.mem_univ s)).trans hmη

/-! ## Congruence in the MDP: only reward and discount matter -/

theorem optOp_congr (U : RowFamily State Action) {M M' : DiscountedMDP State Action}
    (hr : M.reward = M'.reward) (hγ : M.discount = M'.discount) : optOp U M = optOp U M' := by
  funext V s
  unfold optOp robustQ
  rw [hr, hγ]

theorem optFix_congr (U : RowFamily State Action) {M M' : DiscountedMDP State Action}
    (hr : M.reward = M'.reward) (hγ : M.discount = M'.discount) : optFix U M = optFix U M' := by
  apply eq_optFix
  rw [← optOp_congr U hr hγ]
  exact optFix_spec U M

theorem policyOp_congr (U : RowFamily State Action) {M M' : DiscountedMDP State Action}
    (hr : M.reward = M'.reward) (hγ : M.discount = M'.discount)
    (π : StationaryPolicy State Action) : policyOp U M π = policyOp U M' π := by
  funext V s
  unfold policyOp
  rw [hr, hγ]

theorem policyFix_congr (U : RowFamily State Action) {M M' : DiscountedMDP State Action}
    (hr : M.reward = M'.reward) (hγ : M.discount = M'.discount)
    (π : StationaryPolicy State Action) : policyFix U M π = policyFix U M' π := by
  apply eq_policyFix
  rw [← policyOp_congr U hr hγ]
  exact policyFix_spec U M π

/-! ## The absorbing model -/

section Absorb

open Classical

/-- Row family with the singleton override `{δ_x}` at state `x`. -/
noncomputable def absorbFamily (U : RowFamily State Action) (x : State) : RowFamily State Action :=
  fun s a ↦ if s = x then {EnvironmentStage.pointMass x} else U s a

/-- Absorbing reward `(1−γ)u`, clamped to `[0,1]`. -/
noncomputable def absorbReward (γ u : ℝ) : ℝ := max 0 (min ((1 - γ) * u) 1)

theorem absorbReward_of_mem {γ u : ℝ} (hγ1 : γ < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - γ)) :
    absorbReward γ u = (1 - γ) * u := by
  have hpos : 0 < 1 - γ := by linarith
  have h1 : (1 - γ) * u ≤ 1 := by
    calc (1 - γ) * u ≤ (1 - γ) * (1 / (1 - γ)) := mul_le_mul_of_nonneg_left hu1 hpos.le
      _ = 1 := by field_simp
  unfold absorbReward
  rw [min_eq_left h1, max_eq_right (mul_nonneg hpos.le hu0)]

theorem abs_absorbReward_sub_le {γ : ℝ} (hγ1 : γ < 1) (u u' : ℝ) :
    |absorbReward γ u - absorbReward γ u'| ≤ (1 - γ) * |u - u'| := by
  have hpos : 0 < 1 - γ := by linarith
  unfold absorbReward
  have hmin : |min ((1 - γ) * u) 1 - min ((1 - γ) * u') 1| ≤ |(1 - γ) * u - (1 - γ) * u'| :=
    abs_min_sub_min_le _ _ 1
  have hmax : |max 0 (min ((1 - γ) * u) 1) - max 0 (min ((1 - γ) * u') 1)| ≤
      |min ((1 - γ) * u) 1 - min ((1 - γ) * u') 1| := by
    rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
  rw [← mul_sub, abs_mul, abs_of_pos hpos] at hmin
  exact hmax.trans hmin

/-- The absorbing MDP: reward `(1−γ)u` (clamped) at `x`; transition and discount unchanged
(the transition is not used by the robust operators, which read the row family). -/
noncomputable def absorbMDP (M : DiscountedMDP State Action) (x : State) (u : ℝ) :
    DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := M.transition
  reward := fun s a ↦ if s = x then absorbReward M.discount u else M.reward s a
  reward_nonneg := by
    intro s a
    split_ifs
    · exact le_max_left _ _
    · exact M.reward_nonneg s a
  reward_le_one := by
    intro s a
    split_ifs
    · exact max_le (by norm_num) (min_le_right _ _)
    · exact M.reward_le_one s a
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

theorem absorbFamily_nonempty (U : RowFamily State Action) (hU : ∀ s a, (U s a).Nonempty)
    (x : State) : ∀ s a, (absorbFamily U x s a).Nonempty := by
  intro s a
  unfold absorbFamily
  split_ifs
  · exact Set.singleton_nonempty _
  · exact hU s a

theorem robustQ_absorb_at (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (x : State) (u : ℝ) (V : State → ℝ) (a : Action) :
    robustQ (absorbFamily U x) (absorbMDP M x u) V x a =
      absorbReward M.discount u + M.discount * V x := by
  unfold robustQ absorbFamily absorbMDP
  simp only [if_true]
  rw [rowInf_singleton, EnvironmentStage.expectation_pointMass]

theorem robustQ_absorb_off (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (x : State) (u : ℝ) (V : State → ℝ) {s : State} (hs : s ≠ x) (a : Action) :
    robustQ (absorbFamily U x) (absorbMDP M x u) V s a = robustQ U M V s a := by
  unfold robustQ absorbFamily absorbMDP
  simp only [hs, if_false]

/-- Coincidence (optimal family): the absorbing fixed point at `u = V⋆(x)` is `V⋆`. -/
theorem absorb_optFix_eq (U : RowFamily State Action) (hU : ∀ s a, (U s a).Nonempty)
    (M : DiscountedMDP State Action) (x : State) :
    optFix (absorbFamily U x) (absorbMDP M x (optFix U M x)) = optFix U M := by
  letI : Nonempty Action := M.action_nonempty
  symm
  apply eq_optFix
  funext s
  have hb := optFix_bounds U hU M x
  by_cases hs : s = x
  · subst hs
    unfold optOp
    have : robustQ (absorbFamily U s) (absorbMDP M s (optFix U M s)) (optFix U M) s =
        fun _ ↦ optFix U M s := by
      funext a
      rw [robustQ_absorb_at, absorbReward_of_mem M.discount_lt_one hb.1 hb.2]
      ring
    show actionMaximum _ = _
    rw [this]
    exact le_antisymm ((Finset.sup'_le_iff _ _).2 (fun _ _ ↦ le_rfl))
      (le_actionMaximum (fun _ ↦ optFix U M s) (Classical.arbitrary Action))
  · unfold optOp
    have : robustQ (absorbFamily U x) (absorbMDP M x (optFix U M x)) (optFix U M) s =
        robustQ U M (optFix U M) s := by
      funext a; exact robustQ_absorb_off U M x _ _ hs a
    show actionMaximum _ = _
    rw [this]
    exact congrFun (optFix_spec U M) s

/-- Coincidence (fixed deterministic policy). -/
theorem absorb_policyFix_eq (U : RowFamily State Action) (hU : ∀ s a, (U s a).Nonempty)
    (M : DiscountedMDP State Action) (x : State) (f : State → Action) :
    policyFix (absorbFamily U x) (absorbMDP M x (policyFix U M (detPolicy f) x)) (detPolicy f) =
      policyFix U M (detPolicy f) := by
  symm
  apply eq_policyFix
  funext s
  have hb := policyFix_bounds U hU M (detPolicy f) x
  rw [policyOp_detPolicy]
  by_cases hs : s = x
  · subst hs
    have := robustQ_absorb_at U M s (policyFix U M (detPolicy f) s) (policyFix U M (detPolicy f))
      (f s)
    unfold robustQ at this
    rw [this, absorbReward_of_mem M.discount_lt_one hb.1 hb.2]
    ring
  · have := robustQ_absorb_off U M x (policyFix U M (detPolicy f) x)
      (policyFix U M (detPolicy f)) hs (f s)
    unfold robustQ at this
    rw [this]
    have h := congrFun (policyFix_spec U M (detPolicy f)) s
    rw [policyOp_detPolicy] at h
    exact h

theorem absorb_robustQ_diff (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (x : State) (u u' : ℝ) (V : State → ℝ) (s : State) (a : Action) :
    |robustQ (absorbFamily U x) (absorbMDP M x u) V s a -
      robustQ (absorbFamily U x) (absorbMDP M x u') V s a| ≤ (1 - M.discount) * |u - u'| := by
  have hpos : 0 ≤ (1 - M.discount) * |u - u'| :=
    mul_nonneg (by linarith [M.discount_lt_one]) (abs_nonneg _)
  by_cases hs : s = x
  · subst hs
    rw [robustQ_absorb_at, robustQ_absorb_at]
    have := abs_absorbReward_sub_le M.discount_lt_one u u'
    rw [show absorbReward M.discount u + M.discount * V s -
      (absorbReward M.discount u' + M.discount * V s) =
      absorbReward M.discount u - absorbReward M.discount u' by ring]
    exact this
  · rw [robustQ_absorb_off U M x u V hs, robustQ_absorb_off U M x u' V hs, sub_self, abs_zero]
    exact hpos

/-- Lipschitz in `u` (optimal family). -/
theorem absorb_optFix_lipschitz (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (x : State) (u u' : ℝ) (s : State) :
    |optFix (absorbFamily U x) (absorbMDP M x u) s - optFix (absorbFamily U x) (absorbMDP M x u') s|
      ≤ |u - u'| := by
  letI : Nonempty Action := M.action_nonempty
  haveI := M.state_nonempty
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have h := fixed_point_dist_le (optOp_shiftBound (absorbFamily U x) (absorbMDP M x u))
    M.discount_nonneg M.discount_lt_one (optFix_spec _ _) (optFix_spec _ _)
    (η := (1 - M.discount) * |u - u'|) (T' := optOp (absorbFamily U x) (absorbMDP M x u'))
    (fun V t ↦ abs_actionMaximum_sub_le (fun a ↦ absorb_robustQ_diff U M x u u' V t a)) s
  change _ ≤ (1 - M.discount) * |u - u'| / (1 - M.discount) at h
  rwa [mul_div_cancel_left₀ _ hpos.ne'] at h

/-- Lipschitz in `u` (fixed deterministic policy). -/
theorem absorb_policyFix_lipschitz (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (x : State) (f : State → Action) (u u' : ℝ) (s : State) :
    |policyFix (absorbFamily U x) (absorbMDP M x u) (detPolicy f) s -
      policyFix (absorbFamily U x) (absorbMDP M x u') (detPolicy f) s| ≤ |u - u'| := by
  haveI := M.state_nonempty
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have h := fixed_point_dist_le
    (policyOp_shiftBound (absorbFamily U x) (absorbMDP M x u) (detPolicy f))
    M.discount_nonneg M.discount_lt_one (policyFix_spec _ _ _) (policyFix_spec _ _ _)
    (η := (1 - M.discount) * |u - u'|)
    (T' := policyOp (absorbFamily U x) (absorbMDP M x u') (detPolicy f))
    (fun V t ↦ by
      rw [policyOp_detPolicy, policyOp_detPolicy]
      have := absorb_robustQ_diff U M x u u' V t (f t)
      unfold robustQ at this
      exact this) s
  change _ ≤ (1 - M.discount) * |u - u'| / (1 - M.discount) at h
  rwa [mul_div_cancel_left₀ _ hpos.ne'] at h

end Absorb

end StatisticalRL.RobustRL.DRVI
