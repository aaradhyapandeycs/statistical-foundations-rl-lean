import Formalization.OfflineRL.LCBQPathwise
import Formalization.MDP.OptimalTrajectoryValue

/-!
# LCB-Q: pessimism (Lemma 6.10, deterministic part)

`lemma:pessimistic-Q`, `offlineRL.tex:1907–1916`; proof `:4530–4672`. On any data sequence on
which the lower recursion `eq:uniform-policy-pessimism-recursion` of Lemma 6.9 holds (for all
`1 ≤ t ≤ T`, all `(s,a)` and all deterministic `π`), the iterates satisfy
`Q_t ≤ Q⋆` and `V_t ≤ V^{π_t} ≤ V⋆` for all `1 ≤ t ≤ T` (`eq:pessimistic-lcbq`).

The argument follows the source: induction on `t` with `π = π⋆` gives `Q_t ≤ Q⋆` and
`V_t ≤ V⋆` (`:4548–4580`); the last strict increase of `V_·(s)` and the minimum
`m = min_s (V^{π_t} − V_t)(s)` give `m ≥ min{0, γm}`, hence `m ≥ 0` (`:4586–4668`).
-/

open scoped BigOperators

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The lower recursion `eq:uniform-policy-pessimism-recursion` (Lemma 6.9(b)) on one data
sequence: for all `1 ≤ t ≤ T`, `(s,a)` and deterministic `π`,
`Q^π(s,a) − Q_t(s,a) ≥ γ Σ_{i=1}^{n_t(s,a)} η_i^{n_t(s,a)} P_{s,a}(V^π − V_{k_i(s,a)−1})`. -/
def lowerRecursion (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    {T : ℕ} (data : Fin T → (S × A) × S) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ (s : S) (a : A) (π : S → A),
    M.discount * ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s a),
        onlineQRateWeight (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s a) (i + 1) *
          (M.transition s a).expectation (fun s' =>
            M.trajectoryExpectedValue (detPolicy π) s' -
              (run M cb δ sel π₀ data (visitTime data (s, a) i)).V s') ≤
      M.trajectoryExpectedQ (detPolicy π) s a - (run M cb δ sel π₀ data t).Q s a

section Facts

/-- `ι > 0` and hence `H ≥ 1` once `T ≥ 1` and `0 < δ < 1`. -/
theorem iota_pos (M : DiscountedMDP S A) {T : ℕ} {δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ)
    (hδ1 : δ < 1) : 0 < iota S A T δ := by
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  unfold iota
  apply Real.log_pos
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rw [lt_div_iff₀ hδ, one_mul]
  have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A * T := by
    have := mul_le_mul hS hA zero_le_one (by linarith)
    have := mul_le_mul this hT' zero_le_one (by positivity)
    simpa using this
  linarith

theorem horizon_pos (M : DiscountedMDP S A) {T : ℕ} {δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ)
    (hδ1 : δ < 1) : 0 < horizon M.discount (iota S A T δ) := by
  unfold horizon
  apply Nat.ceil_pos.2
  have := iota_pos M hT hδ hδ1
  have h1 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  positivity

theorem sum_rateWeight_range_eq_one {H n : ℕ} (hH : 0 < H) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) = 1 := by
  rw [← sum_Icc_one_eq_sum_range (fun i => onlineQRateWeight H n i)]
  exact onlineQRateWeight_sum_eq_one hH hn

/-- A weighted average of expectations of functions bounded below by `c`. -/
theorem weighted_expectation_ge {H n : ℕ} (hH : 0 < H) (P : FiniteDistribution S)
    (f : ℕ → S → ℝ) (c : ℝ) (hf : ∀ i < n, ∀ s', c ≤ f i s') :
    c * ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) ≤
      ∑ i ∈ Finset.range n, onlineQRateWeight H n (i + 1) * P.expectation (f i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [mul_comm c]
  apply mul_le_mul_of_nonneg_left _ (onlineQRateWeight_nonneg hH n (i + 1))
  calc c = P.expectation (fun _ => c) := (FiniteDistribution.expectation_const P c).symm
    _ ≤ P.expectation (f i) := P.expectation_mono (hf i (Finset.mem_range.1 hi))

/-- `V^π(s) = Q^π(s, π(s))` for a deterministic policy. -/
theorem value_det_eq_Q (M : DiscountedMDP S A) (π : S → A) (s : S) :
    M.trajectoryExpectedValue (detPolicy π) s = M.trajectoryExpectedQ (detPolicy π) s (π s) := by
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  exact EnvironmentStage.expectation_pointMass _ _

theorem value_det_nonneg (M : DiscountedMDP S A) (π : S → A) (s : S) :
    0 ≤ M.trajectoryExpectedValue (detPolicy π) s := by
  rw [value_det_eq_Q, M.trajectoryExpectedQ_eq_policyFixedPoint]
  exact (M.policyFixedPoint_bounds _ s (π s)).1

/-- `V⋆(s) = max_a Q⋆(s,a)`. -/
theorem optValue_eq (M : DiscountedMDP S A) [Nonempty A] (s : S) :
    M.trajectoryExpectedValue M.optimalGreedyPolicy s = actionMaximum (M.optimalityFixedPoint s) := by
  have h := value_det_eq_Q M M.optimalGreedyAction s
  change M.trajectoryExpectedValue M.optimalGreedyPolicy s =
    M.trajectoryExpectedQ M.optimalGreedyPolicy s (M.optimalGreedyAction s) at h
  rw [h, M.optimalGreedy_trajectoryQ, M.optimalGreedyAction_max]

theorem actionMaximum_eq_sel [Nonempty A] {sel : (A → ℝ) → A}
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (f : A → ℝ) :
    actionMaximum f = f (sel f) :=
  le_antisymm (Finset.sup'_le _ _ (fun a _ => hsel f a)) (le_actionMaximum f (sel f))

end Facts

section Pessimism

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S)

/-- `V_u ≤ V⋆` for all `u ≤ T`, and `Q_t ≤ Q⋆` for `1 ≤ t ≤ T`, on the lower-recursion event
(`offlineRL.tex:4548–4580`). -/
theorem run_le_opt_of_lowerRecursion (hδ : 0 < δ) (hδ1 : δ < 1)
    (h : lowerRecursion M cb δ sel π₀ data) :
    (∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤
        M.trajectoryExpectedValue M.optimalGreedyPolicy s) ∧
      ∀ t, 1 ≤ t → t ≤ T → ∀ s a,
        (run M cb δ sel π₀ data t).Q s a ≤ M.optimalityFixedPoint s a := by
  letI : Nonempty A := M.action_nonempty
  -- the Q-step: from the V-bound at all earlier times
  have hQstep : ∀ t, 1 ≤ t → t ≤ T →
      (∀ u, u < t → ∀ s, (run M cb δ sel π₀ data u).V s ≤
        M.trajectoryExpectedValue M.optimalGreedyPolicy s) →
      ∀ s a, (run M cb δ sel π₀ data t).Q s a ≤ M.optimalityFixedPoint s a := by
    intro t ht1 htT hV s a
    have hH := horizon_pos M (le_trans ht1 htT) hδ hδ1
    have hb := h t ht1 htT s a M.optimalGreedyAction
    change M.discount * ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s a),
        onlineQRateWeight (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s a) (i + 1) *
          (M.transition s a).expectation (fun s' =>
            M.trajectoryExpectedValue M.optimalGreedyPolicy s' -
              (run M cb δ sel π₀ data (visitTime data (s, a) i)).V s') ≤
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a - (run M cb δ sel π₀ data t).Q s a at hb
    rw [M.optimalGreedy_trajectoryQ] at hb
    have hsum := weighted_expectation_ge (n := (run M cb δ sel π₀ data t).count s a) hH
      (M.transition s a)
      (fun i s' => M.trajectoryExpectedValue M.optimalGreedyPolicy s' -
        (run M cb δ sel π₀ data (visitTime data (s, a) i)).V s') 0 (by
        intro i hi s'
        have hcnt := run_count M cb δ sel π₀ data htT s a
        rw [hcnt] at hi
        have hlt := visitTime_lt data hi
        have := hV _ hlt s'
        linarith)
    rw [zero_mul] at hsum
    have := mul_nonneg M.discount_nonneg hsum
    linarith
  have hVall : ∀ t, t ≤ T → ∀ u, u ≤ t → ∀ s, (run M cb δ sel π₀ data u).V s ≤
      M.trajectoryExpectedValue M.optimalGreedyPolicy s := by
    intro t
    induction t with
    | zero =>
      intro _ u hu s
      have hu0 : u = 0 := by omega
      subst hu0
      simp only [run_zero, init]
      exact value_det_nonneg M M.optimalGreedyAction s
    | succ t ih =>
      intro htT u hu s
      rcases Nat.lt_or_ge u (t + 1) with hlt | hge
      · exact ih (by omega) u (by omega) s
      · have hu : u = t + 1 := by omega
        subst hu
        have hQ := hQstep (t + 1) (by omega) htT (fun u hu s => ih (by omega) u (by omega) s)
        calc (run M cb δ sel π₀ data (t + 1)).V s
            ≤ max ((run M cb δ sel π₀ data t).V s)
                (actionMaximum ((run M cb δ sel π₀ data (t + 1)).Q s)) :=
              run_V_succ_le M cb δ sel π₀ data (by omega) s
          _ ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s := by
              apply max_le (ih (by omega) t le_rfl s)
              rw [optValue_eq]
              exact Finset.sup'_le _ _ (fun a _ =>
                (hQ s a).trans (le_actionMaximum (M.optimalityFixedPoint s) a))
  refine ⟨fun u hu s => hVall u hu u le_rfl s, fun t ht1 htT => ?_⟩
  exact hQstep t ht1 htT (fun u hu s => hVall t htT u hu.le s)

/-- **Lemma 6.10, deterministic part** (`lemma:pessimistic-Q`, `offlineRL.tex:1907–1916`): on the
lower-recursion event, `Q_t ≤ Q⋆` and `V_t ≤ V^{π_t} ≤ V⋆` for all `1 ≤ t ≤ T`. -/
theorem pessimism_of_lowerRecursion (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (hδ : 0 < δ) (hδ1 : δ < 1) (h : lowerRecursion M cb δ sel π₀ data) :
    ∀ t, 1 ≤ t → t ≤ T →
      (∀ s a, (run M cb δ sel π₀ data t).Q s a ≤ M.optimalityFixedPoint s a) ∧
      ∀ s, (run M cb δ sel π₀ data t).V s ≤
          M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ data t).policy) s ∧
        M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ data t).policy) s ≤
          M.trajectoryExpectedValue M.optimalGreedyPolicy s := by
  letI : Nonempty A := M.action_nonempty
  letI : Nonempty S := M.state_nonempty
  intro t ht1 htT
  have hopt := run_le_opt_of_lowerRecursion M cb δ sel π₀ data hδ hδ1 h
  refine ⟨hopt.2 t ht1 htT, fun s => ⟨?_, M.trajectoryValue_le_optimalGreedy _ s⟩⟩
  set π := (run M cb δ sel π₀ data t).policy with hπ
  set g : S → ℝ := fun s => M.trajectoryExpectedValue (detPolicy π) s -
    (run M cb δ sel π₀ data t).V s with hg
  set m := Finset.univ.inf' Finset.univ_nonempty g with hm
  have hmle : ∀ s, m ≤ g s := fun s => Finset.inf'_le g (Finset.mem_univ s)
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hH := horizon_pos M (le_trans ht1 htT) hδ hδ1
  have hlow : ∀ s, min 0 (M.discount * m) ≤ g s := by
    intro s
    by_cases hpos : 0 < (run M cb δ sel π₀ data t).V s
    · obtain ⟨τ, hτ1, hτt, hτT, hpol, hval⟩ :=
        run_policy_lastIncrease M cb δ sel π₀ data t s hpos
      have hQτ : (run M cb δ sel π₀ data t).V s = (run M cb δ sel π₀ data τ).Q s (π s) := by
        rw [hval, actionMaximum_eq_sel hsel, ← hpol]
      have hb := h τ hτ1 hτT s (π s) π
      have hgs : g s = M.trajectoryExpectedQ (detPolicy π) s (π s) -
          (run M cb δ sel π₀ data τ).Q s (π s) := by
        simp only [hg]
        rw [value_det_eq_Q, hQτ]
      set n := (run M cb δ sel π₀ data τ).count s (π s) with hn
      rcases Nat.eq_zero_or_pos n with hn0 | hn1
      · rw [hn0] at hb
        simp only [Finset.range_zero, Finset.sum_empty, mul_zero] at hb
        rw [hgs]
        exact (min_le_left _ _).trans hb
      · have hsum := weighted_expectation_ge (n := n) hH (M.transition s (π s))
          (fun i s' => M.trajectoryExpectedValue (detPolicy π) s' -
            (run M cb δ sel π₀ data (visitTime data (s, π s) i)).V s') m (by
            intro i hi s'
            have hcnt := run_count M cb δ sel π₀ data hτT s (π s)
            rw [hn, hcnt] at hi
            have hlt := visitTime_lt data hi
            have hmono := run_V_mono M cb δ sel π₀ data (le_of_lt (lt_of_lt_of_le hlt hτt)) s'
            have := hmle s'
            simp only [hg] at this
            linarith)
        rw [sum_rateWeight_range_eq_one hH hn1, mul_one] at hsum
        have hγm := mul_le_mul_of_nonneg_left hsum hγ0
        rw [hgs]
        exact (min_le_right _ _).trans (hγm.trans hb)
    · have hV0 : (run M cb δ sel π₀ data t).V s = 0 :=
        le_antisymm (not_lt.mp hpos) (run_V_nonneg M cb δ sel π₀ data t s)
      have := value_det_nonneg M π s
      simp only [hg, hV0, sub_zero]
      exact (min_le_left _ _).trans this
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty g
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push_neg at hneg
    have h1 := hlow s₀
    rw [← hs₀] at h1
    have hγm : M.discount * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ0 hneg.le
    rw [min_eq_right hγm] at h1
    nlinarith
  have := (hm0.trans (hmle s))
  simp only [hg] at this
  linarith

end Pessimism

end StatisticalRL.OfflineRL.LCBQ
