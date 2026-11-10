import Formalization.RobustRL.LowerBounds.HorizonTrap

/-!
# Corrected Theorem 7.3: the hard RMDP and its exact robust values

Two distinct states `s₀ ≠ s₁` and a distinguished ("good") action `g`. For `t ∈ [0,1]`,
`twoRow t = (1-t) δ_{s₀} + t δ_{s₁}`. The hard model `hardMDP` has reward `0` at `s₀` and `1`
elsewhere, nominal rows `twoRow (ℓ a)` at `s₀` (`ℓ g = lg`, `ℓ a = lb` otherwise) and
`twoRow 1 = δ_{s₁}` elsewhere. For every stationary policy `π`, the robust value under the TV
ball of radius `σ ≤ lb ≤ lg ≤ 1` is computed exactly:
`V^{π,σ}(s₀) = γ w / ((1-γ)(1-γ+γσ+γw))`, `w = E_{a∼π(s₀)} ℓ(a) - σ`
(`hard_robustPolicyValue`).
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound73

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage

section Rows

variable {State : Type*} [Fintype State] [DecidableEq State]

omit [DecidableEq State] in
theorem sum_pair {s₀ s₁ : State} (h : s₀ ≠ s₁) (f : State → ℝ)
    (hf : ∀ x, x ≠ s₀ → x ≠ s₁ → f x = 0) : ∑ x, f x = f s₀ + f s₁ :=
  Finset.sum_eq_add_of_mem s₀ s₁ (Finset.mem_univ _) (Finset.mem_univ _) h
    (fun c _ hc ↦ hf c hc.1 hc.2)

/-- Clamp to `[0,1]` (used only to make `twoRow` total). -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

theorem clamp01_of {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : clamp01 t = t := by
  unfold clamp01; rw [min_eq_left ht1, max_eq_right ht0]

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 :=
  max_le (by norm_num) (min_le_right _ _)

/-- `twoRow h t = (1-t) δ_{s₀} + t δ_{s₁}` (with `t` clamped to `[0,1]`). -/
noncomputable def twoRow {s₀ s₁ : State} (h : s₀ ≠ s₁) (t : ℝ) : FiniteDistribution State where
  prob x := if x = s₁ then clamp01 t else if x = s₀ then 1 - clamp01 t else 0
  prob_nonneg x := by
    split_ifs
    · exact clamp01_nonneg t
    · linarith [clamp01_le_one t]
    · exact le_rfl
  sum_prob := by
    rw [sum_pair h]
    · simp [h]
    · intro x hx0 hx1
      simp [hx0, hx1]

variable {s₀ s₁ : State} (h : s₀ ≠ s₁)

theorem twoRow_prob_s₀ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (twoRow h t).prob s₀ = 1 - t := by
  simp [twoRow, h, clamp01_of ht0 ht1]

theorem twoRow_prob_s₁ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (twoRow h t).prob s₁ = t := by
  simp [twoRow, clamp01_of ht0 ht1]

theorem twoRow_prob_other (t : ℝ) {x : State} (hx0 : x ≠ s₀) (hx1 : x ≠ s₁) :
    (twoRow h t).prob x = 0 := by
  simp [twoRow, hx0, hx1]

theorem twoRow_expectation {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (W : State → ℝ) :
    (twoRow h t).expectation W = (1 - t) * W s₀ + t * W s₁ := by
  unfold FiniteDistribution.expectation
  rw [sum_pair h, twoRow_prob_s₀ h ht0 ht1, twoRow_prob_s₁ h ht0 ht1]
  intro x hx0 hx1
  rw [twoRow_prob_other h t hx0 hx1, zero_mul]

theorem twoRow_tv {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) :
    (1 / 2 : ℝ) * ∑ x, |(twoRow h t).prob x - (twoRow h t').prob x| = |t - t'| := by
  rw [sum_pair h, twoRow_prob_s₀ h ht0 ht1, twoRow_prob_s₀ h ht0' ht1',
    twoRow_prob_s₁ h ht0 ht1, twoRow_prob_s₁ h ht0' ht1']
  · rw [show 1 - t - (1 - t') = -(t - t') by ring, abs_neg]; ring
  · intro x hx0 hx1
    rw [twoRow_prob_other h t hx0 hx1, twoRow_prob_other h t' hx0 hx1, sub_zero, abs_zero]

end Rows

section TV

variable {State : Type*} [Fintype State]

/-- **TV lemma.** Moving to a row within TV distance `σ` lowers the expectation of a
function with values in `[lo, hi]` by at most `σ (hi - lo)`. -/
theorem tv_expectation_lower {p q : FiniteDistribution State} {σ lo hi : ℝ}
    (hq : q ∈ (tvBall p σ : Set (FiniteDistribution State))) (W : State → ℝ)
    (hlohi : lo ≤ hi) (hlo : ∀ x, lo ≤ W x) (hhi : ∀ x, W x ≤ hi) :
    p.expectation W - σ * (hi - lo) ≤ q.expectation W := by
  have hq' : (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x| ≤ σ := hq
  set c := (hi + lo) / 2 with hc
  have key : q.expectation W - p.expectation W =
      ∑ x, (q.prob x - p.prob x) * (W x - c) := by
    have h1 : ∑ x, (q.prob x - p.prob x) * (W x - c) =
        ∑ x, q.prob x * W x - ∑ x, p.prob x * W x - c * (∑ x, q.prob x - ∑ x, p.prob x) := by
      calc ∑ x, (q.prob x - p.prob x) * (W x - c)
          = ∑ x, (q.prob x * W x - p.prob x * W x - (c * q.prob x - c * p.prob x)) :=
            Finset.sum_congr rfl (fun x _ ↦ by ring)
        _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
            ring
    rw [h1, q.sum_prob, p.sum_prob]
    unfold FiniteDistribution.expectation
    ring
  have hterm : ∀ x, -(|p.prob x - q.prob x| * ((hi - lo) / 2)) ≤
      (q.prob x - p.prob x) * (W x - c) := by
    intro x
    have h1 : |W x - c| ≤ (hi - lo) / 2 :=
      abs_le.mpr ⟨by linarith [hlo x, hhi x], by linarith [hlo x, hhi x]⟩
    have h2 : |(q.prob x - p.prob x) * (W x - c)| ≤ |p.prob x - q.prob x| * ((hi - lo) / 2) := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    exact (neg_le_neg h2).trans (neg_abs_le _)
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦ hterm x)
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul] at hsum
  have hhl : 0 ≤ (hi - lo) / 2 := by linarith
  have hS : (∑ x, |p.prob x - q.prob x|) * ((hi - lo) / 2) ≤ σ * (hi - lo) := by
    have := mul_le_mul_of_nonneg_right hq' (by linarith : (0 : ℝ) ≤ hi - lo)
    nlinarith
  linarith

end TV

section Comparison

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Sub-solutions of the policy Bellman equation lie below the actual trajectory value. -/
theorem le_trajectoryValue_of_le_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (W : State → ℝ)
    (hW : ∀ s, W s ≤ M.valueBellman π W s) (s : State) :
    W s ≤ M.trajectoryExpectedValue π s := by
  rw [M.trajectoryExpectedValue_eq_valueFixedPoint]
  set V := M.valueFixedPoint π with hVdef
  have hV := M.valueFixedPoint_spec π
  haveI := M.state_nonempty
  obtain ⟨s', -, hmin⟩ := Finset.exists_min_image Finset.univ (fun t ↦ V t - W t)
    Finset.univ_nonempty
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hstep : ∀ t, M.discount * (V s' - W s') ≤ V t - W t := by
    intro t
    have h1 : V t = M.valueBellman π V t := (congrFun hV t).symm
    have h2 := hW t
    unfold DiscountedMDP.valueBellman at h1 h2
    have h3 : V s' - W s' ≤ (M.policyTransition π t).expectation (fun x ↦ V x - W x) := by
      calc V s' - W s' = (M.policyTransition π t).expectation (fun _ ↦ V s' - W s') :=
            (FiniteDistribution.expectation_const _ _).symm
        _ ≤ _ := FiniteDistribution.expectation_mono _ (fun x ↦ hmin x (Finset.mem_univ x))
    rw [FiniteDistribution.expectation_sub] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 hγ0
    linarith
  have hs' := hstep s'
  have hm : 0 ≤ V s' - W s' := by nlinarith
  linarith [hmin s (Finset.mem_univ s)]

/-- Expansion of the policy Bellman operator of `withKernel M K`. -/
theorem valueBellman_withKernel (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (π : StationaryPolicy State Action)
    (W : State → ℝ) (s : State) :
    (withKernel M K).valueBellman π W s =
      (π s).expectation (fun a ↦ M.reward s a + M.discount * (K s a).expectation W) := by
  rw [DiscountedMDP.valueBellman, DiscountedMDP.policyTransition,
    FiniteDistribution.expectation_bind, ← FiniteDistribution.expectation_mul,
    ← FiniteDistribution.expectation_add]
  rfl

end Comparison

section Model

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

/-- Nominal leave probability of action `a` at `s₀`. -/
def ell (g : Action) (lg lb : ℝ) (a : Action) : ℝ := if a = g then lg else lb

/-- The hard RMDP. -/
noncomputable def hardMDP {s₀ s₁ : State} (h : s₀ ≠ s₁) (g : Action) (γ lg lb : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : DiscountedMDP State Action where
  state_nonempty := ⟨s₀⟩
  action_nonempty := ⟨g⟩
  transition s a := if s = s₀ then twoRow h (ell g lg lb a) else twoRow h 1
  reward s _ := if s = s₀ then 0 else 1
  reward_nonneg s _ := by split_ifs <;> norm_num
  reward_le_one s _ := by split_ifs <;> norm_num
  discount := γ
  discount_nonneg := hγ0
  discount_lt_one := hγ1

/-- Closed-form robust value at `s₀` as a function of the robust leave probability `w`. -/
noncomputable def yfun (γ σ w : ℝ) : ℝ := γ * w / ((1 - γ) * (1 - γ + γ * σ + γ * w))

theorem expectation_ell (g : Action) (lg lb : ℝ) (p : FiniteDistribution Action) :
    p.expectation (ell g lg lb) = lb + p.prob g * (lg - lb) := by
  have hfun : ell g lg lb = fun a ↦ lb + (if a = g then lg - lb else 0) := by
    funext a; unfold ell; split_ifs <;> ring
  rw [hfun, FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
  unfold FiniteDistribution.expectation
  simp [mul_ite, Finset.sum_ite_eq']

variable {s₀ s₁ : State} (h : s₀ ≠ s₁) (g : Action) {γ σ lg lb : ℝ} (hγ0 : 0 ≤ γ)
  (hγ1 : γ < 1)

/-- **Exact robust value** of every stationary policy at `s₀` in the hard RMDP. -/
theorem hard_robustPolicyValue (hσ0 : 0 ≤ σ) (hσlb : σ ≤ lb) (hlb : lb ≤ lg) (hlg : lg ≤ 1)
    (π : StationaryPolicy State Action) :
    robustPolicyValue tvBall (hardMDP h g γ lg lb hγ0 hγ1) σ π s₀ =
      yfun γ σ ((π s₀).expectation (ell g lg lb) - σ) := by
  set M := hardMDP h g γ lg lb hγ0 hγ1 with hM
  set w := (π s₀).expectation (ell g lg lb) - σ with hw
  have hell0 : ∀ a, lb ≤ ell g lg lb a := by intro a; unfold ell; split_ifs <;> linarith
  have hell1 : ∀ a, ell g lg lb a ≤ lg := by intro a; unfold ell; split_ifs <;> linarith
  have hw0 : 0 ≤ w := by
    have := FiniteDistribution.expectation_mono (π s₀) hell0
    rw [FiniteDistribution.expectation_const] at this
    linarith
  set D := 1 - γ + γ * σ + γ * w with hD
  have hDpos : 0 < D := by
    have : 0 ≤ γ * σ := mul_nonneg hγ0 hσ0
    have : 0 ≤ γ * w := mul_nonneg hγ0 hw0
    linarith
  set d := 1 / D with hd
  have hdpos : 0 < d := by positivity
  set y := yfun γ σ w with hy
  set x := y + d with hx
  set W : State → ℝ := fun s ↦ if s = s₀ then y else x with hW
  have hWs₀ : W s₀ = y := by simp [hW]
  have hWs₁ : W s₁ = x := by simp [hW, h.symm]
  have hWlo : ∀ s, y ≤ W s := by intro s; simp only [hW]; split_ifs <;> linarith
  have hWhi : ∀ s, W s ≤ x := by intro s; simp only [hW]; split_ifs <;> linarith
  have h1γ : 0 < 1 - γ := by linarith
  -- algebraic identities for `y` and `x`
  have hyeq : γ * (y + w * d) = y := by
    simp only [hy, hd, yfun]
    field_simp
    ring
  have hxeq : 1 + γ * (x - σ * d) = x := by
    simp only [hx, hy, hd, yfun]
    field_simp
    ring
  -- row expectations of `W`
  have hrow : ∀ t, 0 ≤ t → t ≤ 1 → (twoRow h t).expectation W = y + t * d := by
    intro t ht0 ht1
    rw [twoRow_expectation h ht0 ht1, hWs₀, hWs₁, hx]
    ring
  have hell01 : ∀ a, 0 ≤ ell g lg lb a ∧ ell g lg lb a ≤ 1 := fun a ↦
    ⟨by linarith [hell0 a], by linarith [hell1 a]⟩
  -- the robust Bellman identity `(*)`
  have hstar : ∀ s, (π s).expectation (fun a ↦ M.reward s a +
      γ * ((M.transition s a).expectation W - σ * d)) = W s := by
    intro s
    by_cases hs : s = s₀
    · subst hs
      have hfun : (fun a ↦ M.reward s a + γ * ((M.transition s a).expectation W - σ * d)) =
          fun a ↦ γ * (y - σ * d) + (γ * d) * ell g lg lb a := by
        funext a
        simp only [hM, hardMDP, if_true]
        rw [hrow _ (hell01 a).1 (hell01 a).2]
        ring
      rw [hfun, FiniteDistribution.expectation_add, FiniteDistribution.expectation_const,
        FiniteDistribution.expectation_mul, hWs₀]
      have : (π s).expectation (ell g lg lb) = w + σ := by rw [hw]; ring
      rw [this]
      linarith [hyeq]
    · have hfun : (fun a ↦ M.reward s a + γ * ((M.transition s a).expectation W - σ * d)) =
          fun _ ↦ 1 + γ * (x - σ * d) := by
        funext a
        simp only [hM, hardMDP, if_neg hs]
        rw [hrow 1 (by norm_num) le_rfl]
        ring
      rw [hfun, FiniteDistribution.expectation_const, hxeq]
      simp [hW, hs]
  -- lower bound over every admissible kernel
  have hlower : ∀ K, RobustAdmissible tvBall M σ K →
      y ≤ (withKernel M K).trajectoryExpectedValue π s₀ := by
    intro K hK
    rw [← hWs₀]
    apply le_trajectoryValue_of_le_bellman
    intro s
    rw [valueBellman_withKernel]
    calc W s = (π s).expectation (fun a ↦ M.reward s a +
          γ * ((M.transition s a).expectation W - σ * d)) := (hstar s).symm
      _ ≤ (π s).expectation (fun a ↦ M.reward s a + M.discount * (K s a).expectation W) := by
        apply FiniteDistribution.expectation_mono
        intro a
        have htv := tv_expectation_lower (hK s a) W (by linarith) hWlo hWhi
        have hxy : x - y = d := by rw [hx]; ring
        rw [hxy] at htv
        have : M.discount = γ := rfl
        rw [this]
        nlinarith
  -- the adversarial kernel attains the bound
  let Kstar : State → Action → FiniteDistribution State := fun s a ↦
    if s = s₀ then twoRow h (ell g lg lb a - σ) else twoRow h (1 - σ)
  have hσ1 : σ ≤ 1 := by linarith
  have hadm : RobustAdmissible tvBall M σ Kstar := by
    intro s a
    show (1 / 2 : ℝ) * ∑ x, |(M.transition s a).prob x - (Kstar s a).prob x| ≤ σ
    by_cases hs : s = s₀
    · simp only [hM, hardMDP, Kstar, if_pos hs]
      rw [twoRow_tv h (hell01 a).1 (hell01 a).2 (by linarith [hell0 a]) (by linarith [hell1 a])]
      rw [show ell g lg lb a - (ell g lg lb a - σ) = σ by ring, abs_of_nonneg hσ0]
    · simp only [hM, hardMDP, Kstar, if_neg hs]
      rw [twoRow_tv h (by norm_num) le_rfl (by linarith) (by linarith)]
      rw [show (1 : ℝ) - (1 - σ) = σ by ring, abs_of_nonneg hσ0]
  have hKrow : ∀ s a, (Kstar s a).expectation W = (M.transition s a).expectation W - σ * d := by
    intro s a
    by_cases hs : s = s₀
    · simp only [hM, hardMDP, Kstar, if_pos hs]
      rw [hrow _ (by linarith [hell0 a]) (by linarith [hell1 a]),
        hrow _ (hell01 a).1 (hell01 a).2]
      ring
    · simp only [hM, hardMDP, Kstar, if_neg hs]
      rw [hrow _ (by linarith) (by linarith), hrow 1 (by norm_num) le_rfl]
      ring
  have hfix : (withKernel M Kstar).valueBellman π W = W := by
    funext s
    rw [valueBellman_withKernel]
    rw [← hstar s]
    congr 1
    funext a
    rw [hKrow s a]
    rfl
  have hattain : (withKernel M Kstar).trajectoryExpectedValue π s₀ = y := by
    rw [(withKernel M Kstar).trajectoryExpectedValue_eq_valueFixedPoint,
      ← ((withKernel M Kstar).valueFixedPoint_characterization π W).mp hfix, hWs₀]
  apply le_antisymm
  · apply csInf_le
    · exact ⟨y, by rintro v ⟨K, hK, rfl⟩; exact hlower K hK⟩
    · exact ⟨Kstar, hadm, hattain.symm⟩
  · apply le_csInf
    · exact ⟨_, Kstar, hadm, rfl⟩
    · rintro v ⟨K, hK, rfl⟩
      exact hlower K hK

end Model

end StatisticalRL.RobustRL.Ch7.LowerBound73
