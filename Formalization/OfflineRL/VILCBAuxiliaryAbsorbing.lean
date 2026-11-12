import Formalization.OfflineRL.PreliminaryFacts

/-!
# The auxiliary state-absorbing pessimistic operator (proof of Lemma 6.6, Steps 1–4)

Source: `chapters/offlineRL.tex`, proof of `lem:Bernstein-infinite` (from line 3630).

- Step 1 (`:3672–3711`): for a state `s` and a scalar `u`, the auxiliary MDP `M̂^{s,u}` makes `s`
  absorbing with reward `u` and keeps every other row of the empirical MDP. Its operator
  `T^{s,u}_pess` is `eq:empirical-Bellman-infinite-Lemma8`. At state `s` the auxiliary row is a point
  mass, so its variance vanishes and the penalty is the constant `eq:defn-bsu-sa-inf` (`bonusAbs`,
  see `bonus_eq_bonusAbs_of_variance_eq_zero`). Rows `s' ≠ s` are the rows of `T_pess`.
- Step 2 (`:3713–3864`): at `u⋆ = (1-γ) V̂⋆_pe(s) + min_a b^{s,u}(s,a) + …` the fixed point has
  value `V̂⋆_pe` (`value_auxFix_ustar`).
- Step 3 (`:3940–3962`): for `u ≤ u_max` the operator maps the box into itself and is a
  `γ`-contraction, so it has a unique fixed point in the box (`auxFix`).
- Step 4 (`:3994–4030`): the fixed point is `1/(1-γ)`-Lipschitz in `u` (`auxFix_lipschitz`).

The source writes `min{2c_b log(N/((1-γ)δ))/((1-γ) max_a N_{s,a}), 1/(1-γ)} + 5/N` for
`min_a b^{s,u}(s,a)`; here `minBonusAbs` is literally `min_a bonusAbs s a`, which equals that
expression whenever some `N_{s,a} > 0`.
-/

open scoped BigOperators NNReal

namespace StatisticalRL.OfflineVILCB.Input

open StatisticalRL

variable {S A : Type*} [Fintype S] [Fintype A] (M : Input S A)

/-- The penalty of the auxiliary MDP at the absorbing state (`eq:defn-bsu-sa-inf`, `:3731–3735`),
with the zero-count convention of `def:bonus-Bernstein-infinite`. -/
noncomputable def bonusAbs (s : S) (a : A) : ℝ :=
  if M.count s a = 0 then 1 / (1 - M.γ) + 5 / M.N
  else min (2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a)) (1 / (1 - M.γ)) + 5 / M.N

/-- `eq:defn-bsu-sa-inf`: the source penalty formula at a zero-variance row is `bonusAbs`. -/
theorem bonus_eq_bonusAbs_of_variance_eq_zero (s : S) (a : A) (V : S → ℝ)
    (h : (M.Phat s a).variance V = 0) : M.bonus s a V = M.bonusAbs s a := by
  unfold bonus bonusAbs
  split_ifs with h0
  · rfl
  · have hn : (0 : ℝ) < M.count s a := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hβ : 0 < 2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a) := by
      have := M.cb_pos; have := M.logTerm_pos; have := M.one_sub_γ_pos; positivity
    rw [h, mul_zero, Real.sqrt_zero, max_eq_right hβ.le]

theorem five_div_le_bonusAbs (s : S) (a : A) : 5 / (M.N : ℝ) ≤ M.bonusAbs s a := by
  have hC : 0 < 1 / (1 - M.γ) := by have := M.one_sub_γ_pos; positivity
  unfold bonusAbs
  split_ifs with h0
  · linarith
  · have hn : (0 : ℝ) < M.count s a := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hβ : 0 < 2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a) := by
      have := M.cb_pos; have := M.logTerm_pos; have := M.one_sub_γ_pos; positivity
    have := le_min hβ.le hC.le
    linarith

theorem bonusAbs_le (s : S) (a : A) : M.bonusAbs s a ≤ 1 / (1 - M.γ) + 5 / M.N := by
  unfold bonusAbs
  split_ifs
  · exact le_rfl
  · linarith [min_le_right (2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a)) (1 / (1 - M.γ))]

variable [Nonempty A]

/-- `min_a b^{s,u}(s,a)`. -/
noncomputable def minBonusAbs (s : S) : ℝ := Finset.univ.inf' Finset.univ_nonempty (M.bonusAbs s)

/-- `u_max = min_a b^{s,u}(s,a) + 1` (`:3873–3883`). -/
noncomputable def uMax (s : S) : ℝ := M.minBonusAbs s + 1

/-- `u⋆ = (1-γ) V̂⋆_pe(s) + min_a b^{s,u}(s,a)` (`eq:choice-ustar-offline-mb-proof`). -/
noncomputable def ustar (Q : S → A → ℝ) (s : S) : ℝ := (1 - M.γ) * value Q s + M.minBonusAbs s

theorem minBonusAbs_le (s : S) (a : A) : M.minBonusAbs s ≤ M.bonusAbs s a :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem five_div_le_minBonusAbs (s : S) : 5 / (M.N : ℝ) ≤ M.minBonusAbs s :=
  Finset.le_inf' _ _ fun a _ => M.five_div_le_bonusAbs s a

theorem minBonusAbs_le_bound (s : S) : M.minBonusAbs s ≤ 1 / (1 - M.γ) + 5 / M.N := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact (M.minBonusAbs_le s a).trans (M.bonusAbs_le s a)

open Classical in
/-- The auxiliary pessimistic operator `T^{s,u}_pess` (`eq:empirical-Bellman-infinite-Lemma8`):
at the absorbing state `s` the backup is `max{u − b^{s,u}(s,a) + γ V(s), 0}`; at `s' ≠ s` it is
the original `T_pess`. -/
noncomputable def auxPess (s : S) (u : ℝ) (Q : S → A → ℝ) : S → A → ℝ :=
  fun s' a => if s' = s then max (u - M.bonusAbs s a + M.γ * value Q s) 0 else M.pess Q s' a

theorem auxPess_self (s : S) (u : ℝ) (Q : S → A → ℝ) (a : A) :
    M.auxPess s u Q s a = max (u - M.bonusAbs s a + M.γ * value Q s) 0 := by
  simp [auxPess]

theorem auxPess_of_ne (s : S) (u : ℝ) (Q : S → A → ℝ) {t : S} (ht : t ≠ s) (a : A) :
    M.auxPess s u Q t a = M.pess Q t a := by
  simp [auxPess, ht]

theorem auxPess_mem_box (s : S) {u : ℝ} (hu : u ≤ M.uMax s) (Q : S → A → ℝ) (hQ : Q ∈ M.box) :
    M.auxPess s u Q ∈ M.box := by
  rw [mem_box]
  intro t a
  by_cases ht : t = s
  · subst ht
    rw [auxPess_self]
    refine ⟨le_max_right _ _, max_le ?_ (by have := M.one_sub_γ_pos; positivity)⟩
    have hb := M.minBonusAbs_le t a
    have hV := M.value_le_bound Q hQ t
    have hγ0 := M.γ_nonneg
    have hγ1 := M.one_sub_γ_pos
    have heq : 1 + M.γ * (1 / (1 - M.γ)) = 1 / (1 - M.γ) := by field_simp; ring
    unfold uMax at hu
    nlinarith [mul_le_mul_of_nonneg_left hV hγ0]
  · rw [M.auxPess_of_ne s u Q ht]
    exact (M.mem_box _).1 (M.pess_mem_box Q hQ) t a

theorem auxPess_contract (hγ : 1 / 2 ≤ M.γ) (s : S) (u : ℝ) (Q₁ Q₂ : S → A → ℝ)
    (h₁ : Q₁ ∈ M.box) (h₂ : Q₂ ∈ M.box) (c : ℝ) (hc : ∀ t a, |Q₁ t a - Q₂ t a| ≤ c)
    (t : S) (a : A) :
    |M.auxPess s u Q₁ t a - M.auxPess s u Q₂ t a| ≤ M.γ * c := by
  by_cases ht : t = s
  · subst ht
    rw [auxPess_self, auxPess_self]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have hv := value_abs_sub_le Q₁ Q₂ c hc t
    have heq : u - M.bonusAbs t a + M.γ * value Q₁ t - (u - M.bonusAbs t a + M.γ * value Q₂ t) =
        M.γ * (value Q₁ t - value Q₂ t) := by ring
    rw [heq, abs_mul, abs_of_nonneg M.γ_nonneg]
    exact mul_le_mul_of_nonneg_left hv M.γ_nonneg
  · rw [M.auxPess_of_ne s u Q₁ ht, M.auxPess_of_ne s u Q₂ ht]
    exact M.pess_contract hγ Q₁ Q₂ h₁ h₂ c hc t a

/-- Changing the absorbing reward moves the operator by at most `|u − u'|`. -/
theorem auxPess_param (s : S) (u u' : ℝ) (Q : S → A → ℝ) (t : S) (a : A) :
    |M.auxPess s u Q t a - M.auxPess s u' Q t a| ≤ |u - u'| := by
  by_cases ht : t = s
  · subst ht
    rw [auxPess_self, auxPess_self]
    refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
    congr 1
    ring
  · rw [M.auxPess_of_ne s u Q ht, M.auxPess_of_ne s u' Q ht, sub_self, abs_zero]
    exact abs_nonneg _

/-- `T^{s,u}_pess` restricted to the box. -/
noncomputable def auxBoxMap (s : S) (u : ℝ) (hu : u ≤ M.uMax s) : M.box → M.box :=
  fun Q => ⟨M.auxPess s u Q.1, M.auxPess_mem_box s hu Q.1 Q.2⟩

theorem auxBoxMap_contracting (hγ : 1 / 2 ≤ M.γ) (s : S) (u : ℝ) (hu : u ≤ M.uMax s) :
    ContractingWith ⟨M.γ, M.γ_nonneg⟩ (M.auxBoxMap s u hu) := by
  constructor
  · rw [← NNReal.coe_lt_coe]
    simpa using M.γ_lt_one
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [NNReal.coe_mk]
    apply dist_le_of_abs _ _ (mul_nonneg M.γ_nonneg dist_nonneg)
    intro t a
    exact M.auxPess_contract hγ s u x.1 y.1 x.2 y.2 _ (abs_le_dist x.1 y.1) t a

/-- `Q̂⋆_{s,u}`: the unique fixed point of `T^{s,u}_pess` in the box (Step 3, `:3955–3962`),
defined when `γ ≥ 1/2` and `u ≤ u_max`; it is `0` outside that range and never used there. -/
noncomputable def auxFix (s : S) (u : ℝ) : S → A → ℝ :=
  if h : 1 / 2 ≤ M.γ ∧ u ≤ M.uMax s then
    haveI : CompleteSpace M.box := M.isClosed_box.completeSpace_coe
    haveI : Nonempty M.box := ⟨⟨0, M.zero_mem_box⟩⟩
    (ContractingWith.fixedPoint (M.auxBoxMap s u h.2) (M.auxBoxMap_contracting h.1 s u h.2)).1
  else 0

theorem auxFix_spec (hγ : 1 / 2 ≤ M.γ) (s : S) {u : ℝ} (hu : u ≤ M.uMax s) :
    M.auxFix s u ∈ M.box ∧ M.auxPess s u (M.auxFix s u) = M.auxFix s u := by
  haveI : CompleteSpace M.box := M.isClosed_box.completeSpace_coe
  haveI : Nonempty M.box := ⟨⟨0, M.zero_mem_box⟩⟩
  have hF := M.auxBoxMap_contracting hγ s u hu
  have hP : M.auxBoxMap s u hu (ContractingWith.fixedPoint _ hF) =
      ContractingWith.fixedPoint _ hF := hF.fixedPoint_isFixedPt
  unfold auxFix
  rw [dif_pos ⟨hγ, hu⟩]
  exact ⟨(ContractingWith.fixedPoint _ hF).2, congrArg Subtype.val hP⟩

theorem auxFix_mem_box (hγ : 1 / 2 ≤ M.γ) (s : S) {u : ℝ} (hu : u ≤ M.uMax s) :
    M.auxFix s u ∈ M.box := (M.auxFix_spec hγ s hu).1

/-- Uniqueness of the fixed point in the box. -/
theorem eq_auxFix (hγ : 1 / 2 ≤ M.γ) (s : S) {u : ℝ} (hu : u ≤ M.uMax s) (Q : S → A → ℝ)
    (hQ : Q ∈ M.box) (hfix : M.auxPess s u Q = Q) : Q = M.auxFix s u := by
  obtain ⟨hFb, hFfix⟩ := M.auxFix_spec hγ s hu
  set F := M.auxFix s u
  have hD : dist Q F ≤ M.γ * dist Q F := by
    apply dist_le_of_abs _ _ (mul_nonneg M.γ_nonneg dist_nonneg)
    intro t a
    have h := M.auxPess_contract hγ s u Q F hQ hFb _ (abs_le_dist Q F) t a
    rwa [hfix, hFfix] at h
  have hγ1 := M.γ_lt_one
  have h0 : dist Q F ≤ 0 := by nlinarith [dist_nonneg (x := Q) (y := F)]
  exact dist_le_zero.mp h0

/-- Step 4 (`eq:Qhat-Vhat-ustar-u-gap-offline`): the fixed point is `1/(1-γ)`-Lipschitz in `u`. -/
theorem auxFix_lipschitz (hγ : 1 / 2 ≤ M.γ) (s : S) {u u' : ℝ} (hu : u ≤ M.uMax s)
    (hu' : u' ≤ M.uMax s) (t : S) (a : A) :
    |M.auxFix s u t a - M.auxFix s u' t a| ≤ |u - u'| / (1 - M.γ) := by
  obtain ⟨hFb, hFfix⟩ := M.auxFix_spec hγ s hu
  obtain ⟨hGb, hGfix⟩ := M.auxFix_spec hγ s hu'
  set F := M.auxFix s u
  set G := M.auxFix s u'
  have hD : dist F G ≤ M.γ * dist F G + |u - u'| := by
    apply dist_le_of_abs _ _ (by positivity)
    intro t' a'
    have h1 := M.auxPess_contract hγ s u F G hFb hGb _ (abs_le_dist F G) t' a'
    have h2 := M.auxPess_param s u u' G t' a'
    have hcalc : |M.auxPess s u F t' a' - M.auxPess s u' G t' a'| ≤
        M.γ * dist F G + |u - u'| :=
      calc |M.auxPess s u F t' a' - M.auxPess s u' G t' a'|
          ≤ |M.auxPess s u F t' a' - M.auxPess s u G t' a'| +
            |M.auxPess s u G t' a' - M.auxPess s u' G t' a'| := abs_sub_le _ _ _
        _ ≤ M.γ * dist F G + |u - u'| := add_le_add h1 h2
    rwa [hFfix, hGfix] at hcalc
  have hγ1 := M.one_sub_γ_pos
  have hDle : dist F G ≤ |u - u'| / (1 - M.γ) := by
    rw [le_div_iff₀ hγ1]
    nlinarith
  exact (abs_le_dist F G t a).trans hDle

theorem value_auxFix_mem (hγ : 1 / 2 ≤ M.γ) (s : S) {u : ℝ} (hu : u ≤ M.uMax s) (t : S) :
    0 ≤ value (M.auxFix s u) t ∧ value (M.auxFix s u) t ≤ 1 / (1 - M.γ) :=
  ⟨M.value_nonneg _ (M.auxFix_mem_box hγ s hu) t,
    M.value_le_bound _ (M.auxFix_mem_box hγ s hu) t⟩

theorem value_auxFix_lipschitz (hγ : 1 / 2 ≤ M.γ) (s : S) {u u' : ℝ} (hu : u ≤ M.uMax s)
    (hu' : u' ≤ M.uMax s) (t : S) :
    |value (M.auxFix s u) t - value (M.auxFix s u') t| ≤ |u - u'| / (1 - M.γ) :=
  value_abs_sub_le _ _ _ (M.auxFix_lipschitz hγ s hu hu') t

theorem five_div_le_ustar (Q : S → A → ℝ) (hQ : Q ∈ M.box) (s : S) :
    5 / (M.N : ℝ) ≤ M.ustar Q s := by
  have h1 := M.five_div_le_minBonusAbs s
  have h2 := M.value_nonneg Q hQ s
  have h3 := M.one_sub_γ_pos
  unfold ustar
  nlinarith

theorem ustar_le_uMax (Q : S → A → ℝ) (hQ : Q ∈ M.box) (s : S) : M.ustar Q s ≤ M.uMax s := by
  have h2 := M.value_le_bound Q hQ s
  have h3 := M.one_sub_γ_pos
  have h4 : (1 - M.γ) * value Q s ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h2 h3.le
    rwa [mul_one_div_cancel h3.ne'] at this
  unfold ustar uMax
  linarith

/-- Step 2 (`eq:V-hat-s-ustar-equal-V-pestar`): at `u⋆` the auxiliary fixed point has value
`V̂⋆_pe`. -/
theorem value_auxFix_ustar (hγ : 1 / 2 ≤ M.γ) (Qstar : S → A → ℝ) (hfix : M.pess Qstar = Qstar)
    (s : S) : value (M.auxFix s (M.ustar Qstar s)) = value Qstar := by
  classical
  have hbox := M.fixed_mem_box Qstar hfix
  set V := value Qstar with hVdef
  set us := M.ustar Qstar s with husdef
  let cand : S → A → ℝ := fun t a =>
    if t = s then max (us - M.bonusAbs s a + M.γ * V s) 0 else Qstar t a
  have hV0 := M.value_nonneg Qstar hbox s
  have hterm : ∀ a, us - M.bonusAbs s a + M.γ * V s ≤ V s := by
    intro a
    have := M.minBonusAbs_le s a
    rw [husdef]
    unfold ustar
    linarith
  have hval : value cand = V := by
    funext t
    by_cases ht : t = s
    · subst ht
      apply le_antisymm
      · apply value_le
        intro a
        simp only [cand, if_pos rfl]
        exact max_le (hterm a) hV0
      · obtain ⟨a₀, -, ha₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (M.bonusAbs t)
        have hcand : cand t a₀ = max (us - M.bonusAbs t a₀ + M.γ * V t) 0 := by
          simp only [cand, if_pos rfl]
        have heq : us - M.bonusAbs t a₀ + M.γ * V t = V t := by
          rw [husdef]
          unfold ustar minBonusAbs
          rw [ha₀]
          ring
        calc V t = cand t a₀ := by rw [hcand, heq, max_eq_left hV0]
          _ ≤ value cand t := le_value cand t a₀
    · have hrow : cand t = Qstar t := by
        funext a
        simp only [cand, if_neg ht]
      unfold value
      rw [hrow]
      rfl
  have hcand_box : cand ∈ M.box := by
    rw [mem_box]
    intro t a
    by_cases ht : t = s
    · subst ht
      simp only [cand, if_pos rfl]
      exact ⟨le_max_right _ _, max_le ((hterm a).trans (M.value_le_bound Qstar hbox t))
        (by have := M.one_sub_γ_pos; positivity)⟩
    · simp only [cand, if_neg ht]
      exact (M.mem_box Qstar).1 hbox t a
  have hcand_fix : M.auxPess s us cand = cand := by
    funext t a
    by_cases ht : t = s
    · subst ht
      rw [auxPess_self, hval]
      simp only [cand, if_pos rfl]
    · rw [M.auxPess_of_ne s us cand ht]
      have hp : M.pess cand t a = M.pess Qstar t a := by
        unfold pess
        rw [hval]
      rw [hp, hfix]
      simp only [cand, if_neg ht]
  have hus := M.ustar_le_uMax Qstar hbox s
  have heq := M.eq_auxFix hγ s hus cand hcand_box hcand_fix
  rw [← heq, hval]

end StatisticalRL.OfflineVILCB.Input
