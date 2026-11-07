import Formalization.Online.LowerBound.FamilyDefinitions
import Formalization.MDP.FiniteOptimal
import Formalization.MDP.FiniteTrajectory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Value gap of the two-state gadget (Lemma 5.20)

`lem:Vh-star-Vhpi-gap-lower-bound-online-final` (`chapters/onlineRL.tex:2654–2668`, proof
`:4800–4934`): for every MDP of `C^sub_mdp` and every policy `π`,
`V⋆_1(1) − V^π_1(1) ≥ ∑_{h=1}^H ε₀(H−h)/(16H²) · (1 − π_h(a⋆_h | 1))`.

The argument is carried out for a generic *gadget*: a pair of states `(g, b)` such that at every
stage `g` has reward `1` and moves to `b` with probability `1 − p(a)`, staying at `g` otherwise,
while `b` is absorbing with reward `0` (`IsGadgetStage`). Both the two-state MDP of
`C^sub_mdp` (`g = 1`, `b = 0`) and each copy `j` of the general-`S` MDP (`g = j`, `b = j + ⌊S/2⌋`)
are gadgets.

* `gadget_bad_values`: `V^π(b) = V⋆(b) = 0`.
* `gadget_good_value_lower`: `V^π_h(g) ≥ (H − h + 1)/2` (`eq:Vh-pi-lower-bound-online`, proved by
  direct induction instead of the source's geometric-sum/exponential estimate).
* `gadget_value_gap`: the unrolled recursion `eq:Vh-star-Vhpi-gap-lower-bound-online-simple`,
  `V⋆_1(g) − V^π_1(g) ≥ ∑_h (1 − 1/H)^{h−1} ε(H−h)/(4H²)(1 − π_h(a⋆_h | g))`.
* `one_sub_inv_pow_ge_quarter`: `(1 − 1/H)^H ≥ 1/4` for `H ≥ 2`.
* `onlineLBSub_value_gap` (Lemma 5.20) and `onlineLBStages_value_gap` (each copy of the general
  family).
-/

open scoped BigOperators

namespace StatisticalRL.OnlineLowerBound

open StatisticalRL EnvironmentStage DecisionStage

section Expectation

variable {Ω : Type*} [Fintype Ω]

theorem prob_le_one (d : FiniteDistribution Ω) (x : Ω) : d.prob x ≤ 1 := by
  rw [← d.sum_prob]
  exact Finset.single_le_sum (fun y _ => d.prob_nonneg y) (Finset.mem_univ x)

/-- Expectation under a law with an atom of mass one. -/
theorem expectation_of_prob_eq_one (d : FiniteDistribution Ω) (x : Ω) (hx : d.prob x = 1)
    (V : Ω → ℝ) : d.expectation V = V x := by
  classical
  have hzero : ∀ y, y ≠ x → d.prob y = 0 := by
    intro y hy
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({x, y} : Finset Ω))
      (fun z _ _ => d.prob_nonneg z)
    rw [Finset.sum_pair (Ne.symm hy), d.sum_prob, hx] at hs
    exact le_antisymm (by linarith) (d.prob_nonneg y)
  unfold FiniteDistribution.expectation
  rw [Finset.sum_eq_single x (fun y _ hy => by rw [hzero y hy, zero_mul]) (by simp), hx, one_mul]

/-- Expectation under a law supported on two atoms. -/
theorem expectation_of_two_point (d : FiniteDistribution Ω) (x y : Ω) (hxy : x ≠ y)
    (h : d.prob x + d.prob y = 1) (V : Ω → ℝ) :
    d.expectation V = d.prob x * V x + d.prob y * V y := by
  classical
  have hzero : ∀ z, z ≠ x → z ≠ y → d.prob z = 0 := by
    intro z hzx hzy
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({x, y, z} : Finset Ω))
      (fun w _ _ => d.prob_nonneg w)
    rw [Finset.sum_insert (by simp [hxy, Ne.symm hzx]), Finset.sum_pair (Ne.symm hzy),
      d.sum_prob] at hs
    exact le_antisymm (by linarith) (d.prob_nonneg z)
  unfold FiniteDistribution.expectation
  rw [← Finset.sum_subset (Finset.subset_univ ({x, y} : Finset Ω)) (fun z _ hz => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [hzero z hz.1 hz.2, zero_mul]), Finset.sum_pair hxy]

end Expectation

section Gadget

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A stage acts on the pair `(g, b)` as the two-state gadget of `C^sub_mdp`
(`chapters/onlineRL.tex:2512–2580`): `g` has reward `1` and stays at `g` with probability `p a`,
moving to `b` otherwise; `b` is absorbing with reward `0`. -/
structure IsGadgetStage (e : EnvironmentStage State Action) (g b : State) (p : Action → ℝ) :
    Prop where
  reward_good : ∀ a, e.reward g a = 1
  reward_bad : ∀ a, e.reward b a = 0
  bad_stay : ∀ a, (e.transition b a).prob b = 1
  good_stay : ∀ a, (e.transition g a).prob g = p a
  good_exit : ∀ a, (e.transition g a).prob b = 1 - p a

theorem trajectoryValue_controlled_cons (e : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (π : ℕ → StationaryPolicy State Action)
    (s : State) :
    trajectoryValue (controlled (e :: es) π) s =
      (π 0 s).expectation (fun a => e.reward s a +
        (e.transition s a).expectation (trajectoryValue (controlled es (fun n => π (n + 1))))) := by
  rw [controlled, trajectoryValue_cons]
  rfl

theorem optimalValue_cons' (e : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (s : State) :
    optimalValue (e :: es) s =
      @actionMaximum Action _ e.action_nonempty
        (fun a => e.reward s a + (e.transition s a).expectation (optimalValue es)) := rfl

/-- At the absorbing state of a gadget, every value vanishes. -/
theorem gadget_bad_values {g b : State} :
    ∀ (L : ℕ) (f : Fin L → EnvironmentStage State Action) (p : Fin L → Action → ℝ),
      (∀ n, IsGadgetStage (f n) g b (p n)) → ∀ π : ℕ → StationaryPolicy State Action,
      trajectoryValue (controlled (List.ofFn f) π) b = 0 ∧ optimalValue (List.ofFn f) b = 0
  | 0, f, p, _, π => by
    rw [List.ofFn_zero]
    exact ⟨by simp [controlled], rfl⟩
  | L + 1, f, p, hf, π => by
    obtain ⟨ih1, ih2⟩ := gadget_bad_values _ (fun i => f i.succ) (fun i => p i.succ)
      (fun n => hf n.succ) (fun n => π (n + 1))
    rw [List.ofFn_succ]
    constructor
    · rw [trajectoryValue_controlled_cons]
      have hfun : (fun a => (f 0).reward b a + ((f 0).transition b a).expectation
          (trajectoryValue (controlled (List.ofFn fun i => f i.succ) fun n => π (n + 1)))) =
          fun _ => (0 : ℝ) := by
        funext a
        rw [(hf 0).reward_bad a, expectation_of_prob_eq_one _ b ((hf 0).bad_stay a), ih1]
        ring
      rw [hfun, FiniteDistribution.expectation_const]
    · rw [optimalValue_cons']
      have hfun : (fun a => (f 0).reward b a + ((f 0).transition b a).expectation
          (optimalValue (List.ofFn fun i => f i.succ))) = fun _ => (0 : ℝ) := by
        funext a
        rw [(hf 0).reward_bad a, expectation_of_prob_eq_one _ b ((hf 0).bad_stay a), ih2]
        ring
      rw [hfun]
      unfold actionMaximum
      exact Finset.sup'_const _ _

/-- One-step expectation from the rewarding state of a gadget, given a zero value at `b`. -/
theorem gadget_good_step {g b : State} (hgb : g ≠ b) {e : EnvironmentStage State Action}
    {p : Action → ℝ} (he : IsGadgetStage e g b p) (V : State → ℝ) (hVb : V b = 0) (a : Action) :
    e.reward g a + (e.transition g a).expectation V = 1 + p a * V g := by
  rw [he.reward_good a, expectation_of_two_point _ g b hgb
    (by rw [he.good_stay a, he.good_exit a]; ring) V, he.good_stay a, hVb]
  ring

/-- `V^π_h(g) ≥ (H − h + 1)/2` (`eq:Vh-pi-lower-bound-online`, `chapters/onlineRL.tex:4845–4866`),
stated for a suffix of `L ≤ H` remaining stages. -/
theorem gadget_good_value_lower {g b : State} (hgb : g ≠ b) {H : ℕ} (hH : 1 ≤ H) :
    ∀ (L : ℕ) (f : Fin L → EnvironmentStage State Action) (p : Fin L → Action → ℝ),
      (∀ n, IsGadgetStage (f n) g b (p n)) → (∀ n a, 1 - 1 / (H : ℝ) ≤ p n a) → L ≤ H →
      ∀ π : ℕ → StationaryPolicy State Action,
      (L : ℝ) / 2 ≤ trajectoryValue (controlled (List.ofFn f) π) g
  | 0, f, p, _, _, _, π => by
    rw [List.ofFn_zero]; simp [controlled]
  | L + 1, f, p, hf, hp, hL, π => by
    have ih := gadget_good_value_lower hgb hH _ (fun i => f i.succ) (fun i => p i.succ)
      (fun n => hf n.succ) (fun n a => hp n.succ a) (by omega) (fun n => π (n + 1))
    have hbad := (gadget_bad_values _ (fun i => f i.succ) (fun i => p i.succ)
      (fun n => hf n.succ) (fun n => π (n + 1))).1
    set V' := trajectoryValue (controlled (List.ofFn fun i => f i.succ) fun n => π (n + 1)) with hV'
    rw [List.ofFn_succ, trajectoryValue_controlled_cons]
    rw [← hV']
    simp_rw [gadget_good_step hgb (hf 0) _ hbad]
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
    have hx0 : (0 : ℝ) ≤ 1 / (H : ℝ) := by positivity
    have hxH : 1 / (H : ℝ) * H = 1 := by field_simp
    have hLH : (L : ℝ) + 1 ≤ H := by exact_mod_cast hL
    have hV'0 : 0 ≤ V' g := le_trans (by positivity) ih
    have hmono : (π 0 g).expectation (fun _ => 1 + (1 - 1 / (H : ℝ)) * V' g) ≤
        (π 0 g).expectation (fun a => 1 + p 0 a * V' g) :=
      (π 0 g).expectation_mono fun a => by
        have := mul_le_mul_of_nonneg_right (hp 0 a) hV'0
        linarith
    rw [FiniteDistribution.expectation_const] at hmono
    refine le_trans ?_ hmono
    have h1 : (1 - 1 / (H : ℝ)) * ((L : ℝ) / 2) ≤ (1 - 1 / (H : ℝ)) * V' g :=
      mul_le_mul_of_nonneg_left ih (by
        have : 1 / (H : ℝ) ≤ 1 := by rw [div_le_one hHpos]; exact_mod_cast hH
        linarith)
    have h2 : 1 / (H : ℝ) * L ≤ 1 / (H : ℝ) * (H - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hx0
    push_cast
    nlinarith

/-- The unrolled gap recursion `eq:Vh-star-Vhpi-gap-lower-bound-online-simple`
(`chapters/onlineRL.tex:4885–4933`) for a suffix of `L ≤ H` stages. With 0-based stage index `m`,
the summand is `(1 − 1/H)^m · ε(L − 1 − m)/(4H²) · (1 − π_m(a⋆_m | g))`. -/
theorem gadget_value_gap {g b : State} (hgb : g ≠ b) {H : ℕ} (hH : 1 ≤ H) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ∀ (L : ℕ) (f : Fin L → EnvironmentStage State Action) (p : Fin L → Action → ℝ)
      (astar : Fin L → Action),
      (∀ n, IsGadgetStage (f n) g b (p n)) → (∀ n a, 1 - 1 / (H : ℝ) ≤ p n a) →
      (∀ n a, a ≠ astar n → ε / (2 * (H : ℝ) ^ 2) ≤ p n (astar n) - p n a) → L ≤ H →
      ∀ π : ℕ → StationaryPolicy State Action,
      ∑ m : Fin L, (1 - 1 / (H : ℝ)) ^ (m : ℕ) * (ε * ((L : ℝ) - 1 - m) / (4 * (H : ℝ) ^ 2)) *
          (1 - (π m g).prob (astar m)) ≤
        optimalValue (List.ofFn f) g - trajectoryValue (controlled (List.ofFn f) π) g
  | 0, f, p, astar, _, _, _, _, π => by
    rw [List.ofFn_zero]; simp [controlled, optimalValue]
  | L + 1, f, p, astar, hf, hp, hgap, hL, π => by
    classical
    have ih := gadget_value_gap hgb hH hε _ (fun i => f i.succ) (fun i => p i.succ)
      (fun i => astar i.succ) (fun n => hf n.succ) (fun n a => hp n.succ a)
      (fun n a ha => hgap n.succ a ha) (by omega) (fun n => π (n + 1))
    have hlow := gadget_good_value_lower hgb hH _ (fun i => f i.succ) (fun i => p i.succ)
      (fun n => hf n.succ) (fun n a => hp n.succ a) (by omega) (fun n => π (n + 1))
    have hbad := gadget_bad_values _ (fun i => f i.succ) (fun i => p i.succ)
      (fun n => hf n.succ) (fun n => π (n + 1))
    have hle := trajectoryValue_le_optimal (List.ofFn fun i => f i.succ) (fun n => π (n + 1)) g
    set V' := trajectoryValue (controlled (List.ofFn fun i => f i.succ) fun n => π (n + 1)) with hV'
    set W' := optimalValue (List.ofFn fun i => f i.succ) with hW'
    set κ : ℝ := 1 - 1 / (H : ℝ) with hκ
    set c : ℝ := ε * (L : ℝ) / (4 * (H : ℝ) ^ 2) with hc
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
    have hκ0 : 0 ≤ κ := by
      have : 1 / (H : ℝ) ≤ 1 := by rw [div_le_one hHpos]; exact_mod_cast hH
      linarith
    have hV'0 : (L : ℝ) / 2 ≤ V' g := hlow
    have hD' : 0 ≤ W' g - V' g := by linarith
    -- the one-step inequality
    have hstep : κ * (W' g - V' g) + c * (1 - (π 0 g).prob (astar 0)) ≤
        optimalValue (List.ofFn f) g - trajectoryValue (controlled (List.ofFn f) π) g := by
      rw [List.ofFn_succ, trajectoryValue_controlled_cons, optimalValue_cons']
      rw [← hV', ← hW']
      simp_rw [gadget_good_step hgb (hf 0) _ hbad.1, gadget_good_step hgb (hf 0) _ hbad.2]
      letI : Nonempty Action := (f 0).action_nonempty
      have hW : 1 + p 0 (astar 0) * W' g ≤ actionMaximum (fun a => 1 + p 0 a * W' g) :=
        le_actionMaximum (fun a => 1 + p 0 a * W' g) (astar 0)
      have hpt : ∀ a, κ * (W' g - V' g) + c * (1 - if a = astar 0 then 1 else 0) ≤
          (1 + p 0 (astar 0) * W' g) - (1 + p 0 a * V' g) := by
        intro a
        have h1 : κ * (W' g - V' g) ≤ p 0 (astar 0) * (W' g - V' g) :=
          mul_le_mul_of_nonneg_right (hp 0 (astar 0)) hD'
        by_cases ha : a = astar 0
        · subst ha; simp only [if_true]; nlinarith
        · rw [if_neg ha]
          have h2 := hgap 0 a ha
          have hcoef : 0 ≤ ε / (2 * (H : ℝ) ^ 2) := by positivity
          have h3 : ε / (2 * (H : ℝ) ^ 2) * ((L : ℝ) / 2) ≤
              (p 0 (astar 0) - p 0 a) * V' g :=
            mul_le_mul h2 hV'0 (by positivity) (le_trans hcoef h2)
          have hc' : c = ε / (2 * (H : ℝ) ^ 2) * ((L : ℝ) / 2) := by
            rw [hc]; field_simp; ring
          rw [hc']
          nlinarith
      have hexp := (π 0 g).expectation_mono hpt
      rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const] at hexp
      have hind : (π 0 g).expectation
          (fun a => κ * (W' g - V' g) + c * (1 - if a = astar 0 then 1 else 0)) =
          κ * (W' g - V' g) + c * (1 - (π 0 g).prob (astar 0)) := by
        unfold FiniteDistribution.expectation
        have : ∀ a, (π 0 g).prob a * (κ * (W' g - V' g) + c * (1 - if a = astar 0 then 1 else 0))
            = (κ * (W' g - V' g) + c) * (π 0 g).prob a -
              c * (if a = astar 0 then (π 0 g).prob a else 0) := by
          intro a; split_ifs <;> ring
        simp_rw [this]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (π 0 g).sum_prob,
          Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        ring
      rw [hind] at hexp
      linarith
    refine le_trans ?_ hstep
    rw [Fin.sum_univ_succ]
    have hsum : ∑ m : Fin L, (1 - 1 / (H : ℝ)) ^ ((m.succ : Fin (L + 1)) : ℕ) *
          (ε * (((L + 1 : ℕ) : ℝ) - 1 - ((m.succ : Fin (L + 1)) : ℕ)) / (4 * (H : ℝ) ^ 2)) *
          (1 - (π (m.succ : Fin (L + 1)) g).prob (astar m.succ)) =
        κ * ∑ m : Fin L, (1 - 1 / (H : ℝ)) ^ (m : ℕ) *
          (ε * ((L : ℝ) - 1 - m) / (4 * (H : ℝ) ^ 2)) *
          (1 - (π ((m : ℕ) + 1) g).prob (astar m.succ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Fin.val_succ, pow_succ, hκ]
      push_cast
      ring
    rw [hsum]
    have h0 : (1 - 1 / (H : ℝ)) ^ ((0 : Fin (L + 1)) : ℕ) *
        (ε * (((L + 1 : ℕ) : ℝ) - 1 - ((0 : Fin (L + 1)) : ℕ)) / (4 * (H : ℝ) ^ 2)) *
        (1 - (π ((0 : Fin (L + 1)) : ℕ) g).prob (astar 0)) =
        c * (1 - (π 0 g).prob (astar 0)) := by
      simp only [Fin.val_zero, pow_zero, one_mul, hc]
      push_cast
      ring
    rw [h0]
    have := mul_le_mul_of_nonneg_left ih hκ0
    linarith

/-- `(1 − 1/H)^H ≥ 1/4` for `H ≥ 2` (used at `chapters/onlineRL.tex:4933`). -/
theorem one_sub_inv_pow_ge_quarter {H : ℕ} (hH : 2 ≤ H) : (1 : ℝ) / 4 ≤ (1 - 1 / (H : ℝ)) ^ H := by
  rcases (show H = 2 ∨ H = 3 ∨ 4 ≤ H by omega) with h | h | h
  · subst h; norm_num
  · subst h; norm_num
  · have hH4 : (4 : ℝ) ≤ H := by exact_mod_cast h
    have hpos : (0 : ℝ) < (H : ℝ) - 1 := by linarith
    -- 1 - 1/H ≥ exp(-1/(H-1))
    have hstep : Real.exp (-(1 / ((H : ℝ) - 1))) ≤ 1 - 1 / (H : ℝ) := by
      have h1 := Real.add_one_le_exp (1 / ((H : ℝ) - 1))
      have hexp_pos := Real.exp_pos (1 / ((H : ℝ) - 1))
      rw [Real.exp_neg]
      have heq : 1 - 1 / (H : ℝ) = 1 / (1 / ((H : ℝ) - 1) + 1) := by
        field_simp; ring
      rw [heq, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) h1
    have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hstep H
    rw [← Real.exp_nat_mul] at hpow
    refine le_trans ?_ hpow
    -- exp(-H/(H-1)) ≥ exp(-4/3) ≥ 1/4
    have hratio : -(4 / 3 : ℝ) ≤ (H : ℝ) * -(1 / ((H : ℝ) - 1)) := by
      rw [mul_neg, neg_le_neg_iff, ← div_eq_mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
      linarith
    refine le_trans ?_ (Real.exp_le_exp.mpr hratio)
    have hlog : (4 / 3 : ℝ) ≤ Real.log 4 := by
      have h2 := Real.log_two_gt_d9
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [this]; linarith
    have := (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)).mp hlog
    rw [Real.exp_neg]
    rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (Real.exp_pos _) this

/-- The weighted gap with the constant weight `1/4`: for `2 ≤ H`, `0 ≤ ε`, and `H` gadget stages,
`V⋆_1(g) − V^π_1(g) ≥ ∑_{m<H} ε(H − (m+1))/(16H²)(1 − π_m(a⋆_m | g))`. -/
theorem gadget_value_gap_quarter {g b : State} (hgb : g ≠ b) {H : ℕ} (hH : 2 ≤ H) {ε : ℝ}
    (hε : 0 ≤ ε) (f : Fin H → EnvironmentStage State Action) (p : Fin H → Action → ℝ)
    (astar : Fin H → Action) (hf : ∀ n, IsGadgetStage (f n) g b (p n))
    (hp : ∀ n a, 1 - 1 / (H : ℝ) ≤ p n a)
    (hgap : ∀ n a, a ≠ astar n → ε / (2 * (H : ℝ) ^ 2) ≤ p n (astar n) - p n a)
    (π : ℕ → StationaryPolicy State Action) :
    ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) *
        (1 - (π h g).prob (astar h)) ≤
      optimalValue (List.ofFn f) g - trajectoryValue (controlled (List.ofFn f) π) g := by
  refine le_trans ?_ (gadget_value_gap hgb (by omega) hε _ f p astar hf hp hgap le_rfl π)
  refine Finset.sum_le_sum fun m _ => ?_
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hm : ((m : ℕ) : ℝ) + 1 ≤ H := by exact_mod_cast m.isLt
  have hκ0 : 0 ≤ 1 - 1 / (H : ℝ) := by
    have : 1 / (H : ℝ) ≤ 1 := by
      rw [div_le_one hHpos]; exact_mod_cast (by omega : 1 ≤ H)
    linarith
  have hκ1 : 1 - 1 / (H : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (H : ℝ) := by positivity
    linarith
  have hw : (1 : ℝ) / 4 ≤ (1 - 1 / (H : ℝ)) ^ (m : ℕ) :=
    le_trans (one_sub_inv_pow_ge_quarter hH) (pow_le_pow_of_le_one hκ0 hκ1 m.isLt.le)
  have hrest : 0 ≤ ε * ((H : ℝ) - 1 - m) / (4 * (H : ℝ) ^ 2) * (1 - (π m g).prob (astar m)) :=
    mul_nonneg (div_nonneg (mul_nonneg hε (by linarith)) (by positivity))
      (by linarith [prob_le_one (π m g) (astar m)])
  have heq : ε * ((H : ℝ) - ((m : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) * (1 - (π m g).prob (astar m)) =
      1 / 4 * (ε * ((H : ℝ) - 1 - m) / (4 * (H : ℝ) ^ 2) * (1 - (π m g).prob (astar m))) := by
    field_simp; ring
  rw [heq, mul_assoc ((1 - 1 / (H : ℝ)) ^ (m : ℕ))]
  exact mul_le_mul_of_nonneg_right hw hrest

end Gadget

section Instances

/-- The exit-probability gap of `eqn:prob-astar-a-1`: `q_{a⋆}(a) − q_{a⋆}(a⋆) ≥ ε/(2H²)` for `a ≠ a⋆`
(`chapters/onlineRL.tex:4917–4922`). -/
theorem onlineLBq_gap {H : ℕ} {ε : ℝ} (hH : 1 ≤ H) (hε : 0 ≤ ε) {A : ℕ} (astar a : Fin A)
    (ha : a ≠ astar) :
    ε / (2 * (H : ℝ) ^ 2) ≤ onlineLBq H ε astar a - onlineLBq H ε astar astar := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have h6 : ε / (H : ℝ) ^ 2 = 2 * (ε / (2 * (H : ℝ) ^ 2)) := by field_simp
  have h7 : 0 ≤ ε / (2 * (H : ℝ) ^ 2) := by positivity
  unfold onlineLBq
  by_cases hs : (astar : ℕ) ≠ 0
  · rw [if_pos hs, if_pos hs, if_neg ha, if_pos rfl]
    split_ifs <;> linarith
  · rw [if_neg hs, if_neg hs, if_neg ha, if_pos rfl]
    linarith

theorem onlineLBSubStage_gadget {H : ℕ} {ε : ℝ} (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (astar : Fin A) :
    IsGadgetStage (onlineLBSubStage H ε hH hε hεH astar) 1 0
      (fun a => 1 - onlineLBq H ε astar a) where
  reward_good a := by simp [onlineLBSubStage]
  reward_bad a := by simp [onlineLBSubStage]
  bad_stay a := by simp [onlineLBSubStage, stayRow]
  good_stay a := by simp [onlineLBSubStage, exitRow]
  good_exit a := by simp [onlineLBSubStage, exitRow]

/-- **Lemma 5.20** for the two-state family `C^sub_mdp` (`chapters/onlineRL.tex:2654–2668`). The
source's 1-based step `h` is `(h : Fin H) + 1`. -/
theorem onlineLBSub_value_gap (H A : ℕ) (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) (i : Fin H → Fin A) (π : ℕ → StationaryPolicy (Fin 2) (Fin A)) :
    ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) *
        (1 - (π h 1).prob (i h)) ≤
      optimalValue (List.ofFn (onlineLBSubStages H ε hH hε hεH i)) 1 -
        trajectoryValue (controlled (List.ofFn (onlineLBSubStages H ε hH hε hεH i)) π) 1 := by
  refine gadget_value_gap_quarter (g := (1 : Fin 2)) (b := 0) (by decide) hH hε.le _
    (fun n a => 1 - onlineLBq H ε (i n) a) i
    (fun n => onlineLBSubStage_gadget hH hε hεH (i n)) (fun n a => ?_) (fun n a ha => ?_) π
  · have := (onlineLBq_bounds hH hε hεH (i n) a).2; linarith
  · have := onlineLBq_gap (H := H) (by omega) hε.le (i n) a ha; linarith

/-- Each copy of the general-`S` stage is a gadget on `(j, j + ⌊S/2⌋)`. -/
theorem onlineLBStage_gadget {S H : ℕ} {ε : ℝ} (hS : 2 ≤ S) (hH : 2 ≤ H) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) {A : ℕ} (astar : Fin (S / 2) → Fin A) (j : Fin (S / 2)) :
    IsGadgetStage (onlineLBStage S H ε hS hH hε hεH astar) ⟨j, by omega⟩
      ⟨j + S / 2, by omega⟩ (fun a => 1 - onlineLBq H ε (astar j) a) where
  reward_good a := by simp [onlineLBStage]
  reward_bad a := by simp [onlineLBStage]
  bad_stay a := by simp [onlineLBStage, stayRow]
  good_stay a := by
    have hj := j.isLt
    simp [onlineLBStage, exitRow, hj, Fin.ext_iff, Nat.not_lt.mpr hS]
  good_exit a := by
    have hj := j.isLt
    simp [onlineLBStage, exitRow, hj]

/-- Lemma 5.20 for each copy `j` of the general-`S` family: at the copy's rewarding state `j`,
`V⋆_1(j) − V^π_1(j) ≥ ∑_h ε(H − (h+1))/(16H²)(1 − π_h(i (j, h) | j))`. -/
theorem onlineLBStages_value_gap (S H A : ℕ) (hS : 2 ≤ S) (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) (i : Fin (S / 2) × Fin H → Fin A)
    (π : ℕ → StationaryPolicy (Fin S) (Fin A)) (j : Fin (S / 2)) :
    ∑ h : Fin H, ε * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2) *
        (1 - (π h ⟨j, by omega⟩).prob (i (j, h))) ≤
      optimalValue (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) ⟨j, by omega⟩ -
        trajectoryValue (controlled (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) π)
          ⟨j, by omega⟩ := by
  refine gadget_value_gap_quarter (g := (⟨j, by omega⟩ : Fin S)) (b := ⟨j + S / 2, by omega⟩)
    (fun h => by have := congrArg Fin.val h; simp at this; omega) hH hε.le _
    (fun n a => 1 - onlineLBq H ε (i (j, n)) a) (fun n => i (j, n))
    (fun n => onlineLBStage_gadget hS hH hε hεH (fun j' => i (j', n)) j) (fun n a => ?_)
    (fun n a ha => ?_) π
  · have := (onlineLBq_bounds hH hε hεH (i (j, n)) a).2; linarith
  · have := onlineLBq_gap (H := H) (by omega) hε.le (i (j, n)) a ha; linarith

/-- At every state that is not a copy's rewarding state, both values of the general-`S` family
vanish (absorbing, reward `0`). -/
theorem onlineLBStages_values_nonGood (S H A : ℕ) (hS : 2 ≤ S) (hH : 2 ≤ H) (ε : ℝ) (hε : 0 < ε)
    (hεH : ε ≤ (H : ℝ) / 2) (i : Fin (S / 2) × Fin H → Fin A)
    (π : ℕ → StationaryPolicy (Fin S) (Fin A)) (s : Fin S) (hs : S / 2 ≤ (s : ℕ)) :
    trajectoryValue (controlled (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) π) s = 0 ∧
      optimalValue (List.ofFn (onlineLBStages S H ε hS hH hε hεH i)) s = 0 := by
  -- Induction over the stages: `s` is absorbing with reward `0` at every stage (this also covers the
  -- unused state `2m` when `S` is odd, which is not the absorbing state of any copy).
  suffices h : ∀ (L : ℕ) (f : Fin L → EnvironmentStage (Fin S) (Fin A)),
      (∀ n a, (f n).reward s a = 0 ∧ ((f n).transition s a).prob s = 1) →
      ∀ π : ℕ → StationaryPolicy (Fin S) (Fin A),
      trajectoryValue (controlled (List.ofFn f) π) s = 0 ∧ optimalValue (List.ofFn f) s = 0 by
    refine h _ _ (fun n a => ⟨?_, ?_⟩) π
    · simp [onlineLBStages, onlineLBStage, Nat.not_lt.mpr hs]
    · simp [onlineLBStages, onlineLBStage, Nat.not_lt.mpr hs, stayRow]
  intro L
  induction L with
  | zero => intro f _ π; rw [List.ofFn_zero]; exact ⟨by simp [controlled], rfl⟩
  | succ L ih =>
    intro f hf π
    obtain ⟨ih1, ih2⟩ := ih (fun i => f i.succ) (fun n a => hf n.succ a) (fun n => π (n + 1))
    rw [List.ofFn_succ]
    constructor
    · rw [trajectoryValue_controlled_cons]
      have hfun : (fun a => (f 0).reward s a + ((f 0).transition s a).expectation
          (trajectoryValue (controlled (List.ofFn fun i => f i.succ) fun n => π (n + 1)))) =
          fun _ => (0 : ℝ) := by
        funext a
        rw [(hf 0 a).1, expectation_of_prob_eq_one _ s (hf 0 a).2, ih1]; ring
      rw [hfun, FiniteDistribution.expectation_const]
    · rw [optimalValue_cons']
      have hfun : (fun a => (f 0).reward s a + ((f 0).transition s a).expectation
          (optimalValue (List.ofFn fun i => f i.succ))) = fun _ => (0 : ℝ) := by
        funext a
        rw [(hf 0 a).1, expectation_of_prob_eq_one _ s (hf 0 a).2, ih2]; ring
      rw [hfun]
      unfold actionMaximum
      exact Finset.sup'_const _ _

end Instances

end StatisticalRL.OnlineLowerBound
