import Formalization.RobustRL.LowerBounds.LowerBound73Values
import Formalization.ModelFree.QLearningRobustComparator

/-!
# Corrected Theorem 7.5: exact χ² robust values of the hard RMDP

Reuses the hard model `LowerBound73.hardMDP` (Theorem 7.3, `LowerBound73Values`): reward `0` at `s₀`,
`1` elsewhere; nominal rows `twoRow (ℓ a)` at `s₀` (`ℓ g = lg`, `ℓ a = lb` otherwise) and
`δ_{s₁}` elsewhere. Under the support-aware χ² ball (`chiBall`), the rows `δ_{s₁}` allow no
perturbation, and the row `twoRow ℓ` (`0 < ℓ < 1`) can lower its `s₁`-mass to exactly
`T = ℓ - √(σ ℓ (1-ℓ))` (encoded by `ChiPair σ ℓ T`). For every stationary policy `π`
(`chi_hard_robustPolicyValue`):
`V^{π,σ}(s₀) = γ L / ((1-γ)(1-γ+γL))`, `L = E_{a∼π(s₀)} T(a)`.
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.LowerBound75

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.EnvironmentStage
  StatisticalRL.RobustRL.Ch7.LowerBound73

/-- `T` is the minimal `s₁`-mass in the χ² ball of radius `σ` around `twoRow ℓ`. -/
structure ChiPair (σ ℓ T : ℝ) : Prop where
  pos : 0 < ℓ
  lt_one : ℓ < 1
  nonneg : 0 ≤ T
  le : T ≤ ℓ
  eq : (ℓ - T) ^ 2 = σ * (ℓ * (1 - ℓ))

/-- Closed-form χ² robust value at `s₀` as a function of the robust leave probability. -/
noncomputable def ychi (γ L : ℝ) : ℝ := γ * L / ((1 - γ) * (1 - γ + γ * L))

section Rows

variable {State : Type*} [Fintype State] [DecidableEq State] {s₀ s₁ : State} (h : s₀ ≠ s₁)

omit [DecidableEq State] in
include h in
theorem pair_sum {q : FiniteDistribution State} (hq : ∀ x, x ≠ s₀ → x ≠ s₁ → q.prob x = 0) :
    q.prob s₀ = 1 - q.prob s₁ := by
  have := q.sum_prob
  rw [sum_pair h _ hq] at this
  linarith

omit [DecidableEq State] in
include h in
theorem pair_expectation {q : FiniteDistribution State}
    (hq : ∀ x, x ≠ s₀ → x ≠ s₁ → q.prob x = 0) (W : State → ℝ) :
    q.expectation W = (1 - q.prob s₁) * W s₀ + q.prob s₁ * W s₁ := by
  unfold FiniteDistribution.expectation
  rw [sum_pair h, pair_sum h hq]
  intro x hx0 hx1
  rw [hq x hx0 hx1, zero_mul]

theorem chi_support {ℓ σ : ℝ} {q : FiniteDistribution State}
    (hq : q ∈ QLearning.qChiBall (twoRow h ℓ) σ) : ∀ x, x ≠ s₀ → x ≠ s₁ → q.prob x = 0 :=
  fun x hx0 hx1 ↦ hq.1 x (twoRow_prob_other h ℓ hx0 hx1)

theorem chi_twoRow {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) {q : FiniteDistribution State}
    (hq : ∀ x, x ≠ s₀ → x ≠ s₁ → q.prob x = 0) :
    QLearning.qChiSquared (twoRow h ℓ) q = (q.prob s₁ - ℓ) ^ 2 / (ℓ * (1 - ℓ)) := by
  unfold QLearning.qChiSquared
  rw [Finset.sum_filter, sum_pair h, twoRow_prob_s₀ h hℓ0.le hℓ1.le,
    twoRow_prob_s₁ h hℓ0.le hℓ1.le, if_pos (by linarith), if_pos hℓ0, pair_sum h hq]
  · have h1 : (1 - ℓ) ≠ 0 := by linarith
    field_simp
    ring
  · intro x hx0 hx1
    rw [twoRow_prob_other h ℓ hx0 hx1, if_neg (lt_irrefl 0)]

/-- Every row of the χ² ball around `twoRow ℓ` keeps `s₁`-mass at least `T`. -/
theorem chi_lower {σ ℓ T : ℝ} (hp : ChiPair σ ℓ T) {q : FiniteDistribution State}
    (hq : q ∈ QLearning.qChiBall (twoRow h ℓ) σ) : T ≤ q.prob s₁ := by
  have hs := chi_support h hq
  have hc := hq.2
  rw [chi_twoRow h hp.pos hp.lt_one hs] at hc
  have hv : 0 < ℓ * (1 - ℓ) := mul_pos hp.pos (by linarith [hp.lt_one])
  rw [div_le_iff₀ hv] at hc
  by_contra hlt
  push_neg at hlt
  have h1 : 0 ≤ ℓ - T := by linarith [hp.le]
  have h2 : ℓ - T < ℓ - q.prob s₁ := by linarith
  have h3 : (ℓ - T) ^ 2 < (ℓ - q.prob s₁) ^ 2 := by nlinarith
  have h4 : (q.prob s₁ - ℓ) ^ 2 = (ℓ - q.prob s₁) ^ 2 := by ring
  linarith [hp.eq]

/-- `twoRow T` lies in the χ² ball around `twoRow ℓ`. -/
theorem chi_attain {σ ℓ T : ℝ} (hp : ChiPair σ ℓ T) :
    twoRow h T ∈ QLearning.qChiBall (twoRow h ℓ) σ := by
  have hT1 : T ≤ 1 := by linarith [hp.le, hp.lt_one]
  refine ⟨?_, ?_⟩
  · intro x hx
    by_cases hx1 : x = s₁
    · subst hx1
      rw [twoRow_prob_s₁ h hp.pos.le hp.lt_one.le] at hx
      linarith [hp.pos]
    by_cases hx0 : x = s₀
    · subst hx0
      rw [twoRow_prob_s₀ h hp.pos.le hp.lt_one.le] at hx
      linarith [hp.lt_one]
    exact twoRow_prob_other h T hx0 hx1
  · rw [chi_twoRow h hp.pos hp.lt_one (fun x hx0 hx1 ↦ twoRow_prob_other h T hx0 hx1),
      twoRow_prob_s₁ h hp.nonneg hT1]
    have hv : 0 < ℓ * (1 - ℓ) := mul_pos hp.pos (by linarith [hp.lt_one])
    rw [div_le_iff₀ hv, show (T - ℓ) ^ 2 = (ℓ - T) ^ 2 by ring, hp.eq]

/-- The χ² ball around the point mass `twoRow 1 = δ_{s₁}` is `{δ_{s₁}}` (on expectations). -/
theorem chi_point_expectation {σ : ℝ} {q : FiniteDistribution State}
    (hq : q ∈ QLearning.qChiBall (twoRow h 1) σ) (W : State → ℝ) :
    q.expectation W = W s₁ := by
  have hs := chi_support h hq
  have h0 : q.prob s₀ = 0 := hq.1 s₀ (by rw [twoRow_prob_s₀ h (by norm_num) le_rfl]; ring)
  have h1 : q.prob s₁ = 1 := by have := pair_sum h hs; linarith
  rw [pair_expectation h hs, h1]
  ring

end Rows

section Model

variable {State Action : Type*} [Fintype State] [Fintype Action] [DecidableEq State]
  [DecidableEq Action]

variable {s₀ s₁ : State} (h : s₀ ≠ s₁) (g : Action) {γ σ lg lb Tg Tb : ℝ} (hγ0 : 0 ≤ γ)
  (hγ1 : γ < 1)

/-- **Exact χ² robust value** of every stationary policy at `s₀` in the hard RMDP. -/
theorem chi_hard_robustPolicyValue (hσ0 : 0 ≤ σ) (hpg : ChiPair σ lg Tg)
    (hpb : ChiPair σ lb Tb) (π : StationaryPolicy State Action) :
    robustPolicyValue chiBall (hardMDP h g γ lg lb hγ0 hγ1) σ π s₀ =
      ychi γ ((π s₀).expectation (ell g Tg Tb)) := by
  set M := hardMDP h g γ lg lb hγ0 hγ1 with hM
  set L := (π s₀).expectation (ell g Tg Tb) with hL
  have hpair : ∀ a, ChiPair σ (ell g lg lb a) (ell g Tg Tb a) := by
    intro a; unfold ell; split_ifs
    · exact hpg
    · exact hpb
  have hL0 : 0 ≤ L := by
    have := FiniteDistribution.expectation_mono (π s₀) (fun a ↦ (hpair a).nonneg)
    rwa [FiniteDistribution.expectation_const] at this
  have h1γ : 0 < 1 - γ := by linarith
  have hD : 0 < 1 - γ + γ * L := by have := mul_nonneg hγ0 hL0; linarith
  set y := ychi γ L with hy
  set x := 1 / (1 - γ) with hx
  have hyx : y ≤ x := by
    simp only [hy, hx, ychi]
    rw [div_le_div_iff₀ (by positivity) h1γ]
    nlinarith [mul_nonneg hγ0 hL0]
  set W : State → ℝ := fun s ↦ if s = s₀ then y else x with hW
  have hWs₀ : W s₀ = y := by simp [hW]
  have hWs₁ : W s₁ = x := by simp [hW, h.symm]
  have hyeq : γ * (y + L * (x - y)) = y := by
    simp only [hy, hx, ychi]
    field_simp
    ring
  have hxeq : 1 + γ * x = x := by
    simp only [hx]
    field_simp
    ring
  -- the robust row value `R s a`
  set R : State → Action → ℝ := fun s a ↦ if s = s₀ then y + ell g Tg Tb a * (x - y) else x
    with hR
  have hstar : ∀ s, (π s).expectation (fun a ↦ M.reward s a + γ * R s a) = W s := by
    intro s
    by_cases hs : s = s₀
    · subst hs
      have hfun : (fun a ↦ M.reward s a + γ * R s a) =
          fun a ↦ γ * y + (γ * (x - y)) * ell g Tg Tb a := by
        funext a
        simp only [hM, hardMDP, hR, if_true]
        ring
      rw [hfun, FiniteDistribution.expectation_add, FiniteDistribution.expectation_const,
        FiniteDistribution.expectation_mul, hWs₀, ← hL]
      linarith [hyeq]
    · have hfun : (fun a ↦ M.reward s a + γ * R s a) = fun _ ↦ 1 + γ * x := by
        funext a
        simp only [hM, hardMDP, hR, if_neg hs]
      rw [hfun, FiniteDistribution.expectation_const, hxeq]
      simp [hW, hs]
  -- lower bound over every admissible kernel
  have hlower : ∀ K, RobustAdmissible chiBall M σ K →
      y ≤ (withKernel M K).trajectoryExpectedValue π s₀ := by
    intro K hK
    rw [← hWs₀]
    apply le_trajectoryValue_of_le_bellman
    intro s
    rw [valueBellman_withKernel]
    rw [← hstar s]
    apply FiniteDistribution.expectation_mono
    intro a
    have hKa := hK s a
    have hdisc : M.discount = γ := rfl
    rw [hdisc]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ hγ0
    by_cases hs : s = s₀
    · subst hs
      have hq : K s a ∈ QLearning.qChiBall (twoRow h (ell g lg lb a)) σ := by
        simpa only [hM, hardMDP, if_true, chiBall] using hKa
      have hT := chi_lower h (hpair a) hq
      rw [pair_expectation h (chi_support h hq), hWs₀, hWs₁]
      simp only [hR, if_true]
      nlinarith
    · have hq : K s a ∈ QLearning.qChiBall (twoRow h 1) σ := by
        simpa only [hM, hardMDP, if_neg hs, chiBall] using hKa
      rw [chi_point_expectation h hq, hWs₁]
      simp only [hR, if_neg hs, le_refl]
  -- the adversarial kernel attains the bound
  let Kstar : State → Action → FiniteDistribution State := fun s a ↦
    if s = s₀ then twoRow h (ell g Tg Tb a) else twoRow h 1
  have hadm : RobustAdmissible chiBall M σ Kstar := by
    intro s a
    by_cases hs : s = s₀
    · simp only [hM, hardMDP, Kstar, if_pos hs, chiBall]
      exact chi_attain h (hpair a)
    · simp only [hM, hardMDP, Kstar, if_neg hs, chiBall]
      exact QLearning.qChiBall_self _ σ hσ0
  have hKrow : ∀ s a, (Kstar s a).expectation W = R s a := by
    intro s a
    by_cases hs : s = s₀
    · simp only [Kstar, hR, if_pos hs]
      have hT1 : ell g Tg Tb a ≤ 1 := by linarith [(hpair a).le, (hpair a).lt_one]
      rw [twoRow_expectation h (hpair a).nonneg hT1, hWs₀, hWs₁]
      ring
    · simp only [Kstar, hR, if_neg hs]
      rw [twoRow_expectation h (by norm_num) le_rfl, hWs₀, hWs₁]
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

end StatisticalRL.RobustRL.Ch7.LowerBound75
