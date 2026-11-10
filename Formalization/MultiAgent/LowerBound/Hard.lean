import Formalization.MultiAgent.LowerBound.Values
import Formalization.Online.LowerBound.FamilyDefinitions

/-!
# Corrected Theorem 7.8: the hard family and its value analysis

Own construction (the source gives no proof). Player `istar` (the one with the most actions), a sink
state `z`, and a hidden action `θ(s, h) ∈ Fin (A istar)` for every state `s` and step index `h`.

* At a state `s ≠ z` and step `h`, the next state is `z` with probability
  `q_{θ(s,h)}(a_istar)` (the exit table `onlineLBq H λ` of `chapters/onlineRL.tex:2582–2604`) and `s`
  otherwise; `z` is absorbing. Transitions depend on the joint action only through `a_istar`.
* Rewards are the same for every `θ`: `r_istar(s) = 1[s ≠ z] − cst` and arbitrary rewards `rest` of the
  other players (instantiated later to meet the zero-sum convention).
* `hard_chain_gap`: for every joint policy `π` and chain state `x ≠ z`,
  `gap(π) ≥ ∑_{j < ⌊H/2⌋} (H/8) · (1 − σ_j(θ(x,j))) · λ/(2H²)` where `σ_j` is the `istar`-marginal of
  `π_{1+j}(· | x)`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL OnlineLowerBound

variable {m S H : ℕ} {A : Fin m → ℕ}

theorem stayRow_expectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (z : Ω) (f : Ω → ℝ) :
    (stayRow z).expectation f = f z := by
  unfold FiniteDistribution.expectation stayRow
  simp [ite_mul, Finset.sum_ite_eq']

theorem exitRow_expectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (g b : Ω) (hgb : g ≠ b)
    (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (f : Ω → ℝ) :
    (exitRow g b hgb q h0 h1).expectation f = q * f b + (1 - q) * f g := by
  unfold FiniteDistribution.expectation exitRow
  have h : ∀ x, (if x = b then q else if x = g then 1 - q else 0) * f x =
      (if x = b then q * f b else 0) + (if x = g then (1 - q) * f g else 0) := by
    intro x
    by_cases hb : x = b
    · subst hb; simp [Ne.symm hgb]
    · by_cases hg : x = g
      · subst hg; simp [hb]
      · simp [hb, hg]
  simp only
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Probability that the `i`-th coordinate of a joint action drawn from `d` equals `b`. -/
noncomputable def margProb (d : FiniteDistribution ((i : Fin m) → Fin (A i))) (i : Fin m)
    (b : Fin (A i)) : ℝ :=
  ∑ a, d.prob a * (if a i = b then 1 else 0)

theorem margProb_nonneg (d : FiniteDistribution ((i : Fin m) → Fin (A i))) (i : Fin m)
    (b : Fin (A i)) : 0 ≤ margProb d i b :=
  Finset.sum_nonneg fun a _ => mul_nonneg (d.prob_nonneg a) (by split_ifs <;> norm_num)

theorem sum_margProb (d : FiniteDistribution ((i : Fin m) → Fin (A i))) (i : Fin m) :
    ∑ b, margProb d i b = 1 := by
  unfold margProb
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact d.sum_prob

/-- `onlineLBq` is minimised at the hidden action, with margin `λ/(2H²)` at every other action. -/
theorem onlineLBq_ge_self {H : ℕ} (hH : 1 ≤ H) {lam : ℝ} (hl : 0 ≤ lam) {n : ℕ} (θ b : Fin n) :
    onlineLBq H lam θ θ + (if b = θ then 0 else lam / (2 * (H : ℝ) ^ 2)) ≤ onlineLBq H lam θ b := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have e : lam / (2 * (H : ℝ) ^ 2) = lam / (H : ℝ) ^ 2 / 2 := by field_simp
  have hy : 0 ≤ lam / (H : ℝ) ^ 2 := by positivity
  rw [e]
  unfold onlineLBq
  by_cases hb : b = θ
  · subst hb; simp
  · simp only [hb, if_false]
    split_ifs <;> linarith

section Hard

variable (istar : Fin m) (z : Fin S) (hH : 2 ≤ H) (lam : ℝ) (hl : 0 < lam)
  (hlH : lam ≤ (H : ℝ) / 2)

/-- The step index in `Fin H` of the game step `h` (`h ∈ [1, H]` ↦ `h − 1`). -/
def stepIdx (h : ℕ) : Fin H := ⟨(h - 1) % H, Nat.mod_lt _ (by omega)⟩

theorem stepIdx_one_add (j : ℕ) (hj : j < H) : stepIdx hH (1 + j) = ⟨j, hj⟩ := by
  simp [stepIdx, Nat.mod_eq_of_lt hj]

theorem stepIdx_succ (t : Fin H) : stepIdx hH ((t : ℕ) + 1) = t := by
  ext; simp [stepIdx, Nat.mod_eq_of_lt t.isLt]

/-- Exit probability at step `h`, state `s`, action `b` of player `istar`. -/
noncomputable def exitQ (θ : Fin S × Fin H → Fin (A istar)) (h : ℕ) (s : Fin S)
    (b : Fin (A istar)) : ℝ :=
  onlineLBq H lam (θ (s, stepIdx hH h)) b

/-- Transition kernel of the hard game. -/
noncomputable def hardTrans (θ : Fin S × Fin H → Fin (A istar)) (h : ℕ) (s : Fin S)
    (a : (i : Fin m) → Fin (A i)) : FiniteDistribution (Fin S) :=
  if hs : s = z then stayRow z
  else exitRow s z hs (exitQ istar hH lam θ h s (a istar))
    (onlineLBq_nonneg hH hl hlH _ _) (onlineLBq_le_one hH hl hlH _ _)

/-- Rewards of the hard game (common to all `θ`). -/
noncomputable def hardReward (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ) :
    Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ :=
  fun i h s a => if i = istar then (if s = z then 0 else 1) - cst else rest i h s a

/-- The hard game `MG_θ`. -/
noncomputable def hardGame (cst : ℝ)
    (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ : Fin S × Fin H → Fin (A istar)) : MarkovGame m S H A where
  transition := hardTrans istar z hH lam hl hlH θ
  reward := hardReward istar z cst rest

/-- Mean exit probability of `π` at state `s`, step `h`. -/
noncomputable def ellOf (θ : Fin S × Fin H → Fin (A istar)) (π : JointPolicy m S A) (s : Fin S)
    (h : ℕ) : ℝ :=
  ∑ a, (π h s).prob a * exitQ istar hH lam θ h s (a istar)

/-- The deterministic deviation of `istar` playing the hidden action. -/
noncomputable def piStar (θ : Fin S × Fin H → Fin (A istar)) : PlayerPolicy S (A istar) :=
  fun h s => stayRow (θ (s, stepIdx hH h))

variable {istar z hH lam hl hlH}

theorem hardGame_value (cst : ℝ) (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ : Fin S × Fin H → Fin (A istar)) (π : JointPolicy m S A) :
    ∀ (k h : ℕ) (s : Fin S), valueJ (hardGame istar z hH lam hl hlH cst rest θ) π istar h k s =
      (if s = z then 0 else chainU (ellOf istar hH lam θ π s) h k) - cst * k := by
  intro k
  induction k with
  | zero => intro h s; simp [valueJ, chainU_zero]
  | succ k ih =>
    intro h s
    simp only [valueJ]
    have hr : ∀ a, (hardGame istar z hH lam hl hlH cst rest θ).reward istar h s a =
        (if s = z then 0 else 1) - cst := fun a => by simp [hardGame, hardReward]
    simp_rw [hr]
    by_cases hs : s = z
    · subst hs
      have ht : ∀ a, (hardGame istar s hH lam hl hlH cst rest θ).transition h s a = stayRow s :=
        fun a => by simp [hardGame, hardTrans]
      simp_rw [ht, stayRow_expectation, ih (h + 1) s]
      simp only [if_true]
      rw [← Finset.sum_mul, (π h s).sum_prob]
      push_cast; ring
    · have ht : ∀ a, (hardGame istar z hH lam hl hlH cst rest θ).transition h s a =
          exitRow s z hs (exitQ istar hH lam θ h s (a istar))
            (onlineLBq_nonneg hH hl hlH _ _) (onlineLBq_le_one hH hl hlH _ _) :=
        fun a => by simp [hardGame, hardTrans, hs]
      simp_rw [ht, exitRow_expectation, ih (h + 1)]
      simp only [hs, if_true, if_false]
      rw [chainU_succ]
      set u := chainU (ellOf istar hH lam θ π s) (h + 1) k
      have hsplit : ∀ a, (π h s).prob a * (1 - cst + (exitQ istar hH lam θ h s (a istar) *
          (0 - cst * k) + (1 - exitQ istar hH lam θ h s (a istar)) * (u - cst * k))) =
          (π h s).prob a * (1 - cst - cst * k + u) -
            (π h s).prob a * exitQ istar hH lam θ h s (a istar) * u := fun a => by ring
      simp_rw [hsplit]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, (π h s).sum_prob]
      unfold ellOf
      push_cast; ring

include hl hlH in
theorem ellOf_le (θ : Fin S × Fin H → Fin (A istar)) (π : JointPolicy m S A) (s : Fin S)
    (h : ℕ) : ellOf istar hH lam θ π s h ≤ 1 / (H : ℝ) := by
  unfold ellOf
  calc ∑ a, (π h s).prob a * exitQ istar hH lam θ h s (a istar) ≤ ∑ a, (π h s).prob a * (1 / (H : ℝ)) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (onlineLBq_bounds hH hl hlH _ _).2 ((π h s).prob_nonneg a)
    _ = 1 / (H : ℝ) := by rw [← Finset.sum_mul, (π h s).sum_prob, one_mul]

include hl in
/-- Excess mean exit probability over the hidden action. -/
theorem ellOf_sub_ge (θ : Fin S × Fin H → Fin (A istar)) (π : JointPolicy m S A) (s : Fin S)
    (h : ℕ) :
    (1 - margProb (π h s) istar (θ (s, stepIdx hH h))) * (lam / (2 * (H : ℝ) ^ 2)) ≤
      ellOf istar hH lam θ π s h - exitQ istar hH lam θ h s (θ (s, stepIdx hH h)) := by
  set c := θ (s, stepIdx hH h)
  set y := lam / (2 * (H : ℝ) ^ 2)
  have hge := fun b => onlineLBq_ge_self (H := H) (by omega) hl.le c b
  unfold ellOf margProb
  have e1 : ellOf istar hH lam θ π s h - exitQ istar hH lam θ h s c =
      ∑ a, (π h s).prob a * (exitQ istar hH lam θ h s (a istar) - exitQ istar hH lam θ h s c) := by
    unfold ellOf
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (π h s).sum_prob, one_mul]
  unfold ellOf at e1
  rw [e1]
  have e2 : (1 - ∑ a, (π h s).prob a * (if a istar = c then 1 else 0)) * y =
      ∑ a, (π h s).prob a * (if a istar = c then 0 else y) := by
    have : ∀ a, (π h s).prob a * (if a istar = c then 0 else y) =
        (π h s).prob a * y - (π h s).prob a * (if a istar = c then 1 else 0) * y := by
      intro a; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, (π h s).sum_prob]
    ring
  rw [e2]
  refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((π h s).prob_nonneg a)
  have := hge (a istar)
  unfold exitQ
  linarith

/-- **Per-chain gap.** For a chain state `x ≠ z` and every joint policy `π`,
`gap(π) ≥ ∑_{j < ⌊H/2⌋} (H/8) (1 − σ_j(θ(x,j))) λ/(2H²)`, with `σ_j` the `istar`-marginal of
`π_{1+j}(·|x)`. -/
theorem hard_chain_gap (cst : ℝ) (hcst : 0 ≤ cst)
    (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ)
    (θ : Fin S × Fin H → Fin (A istar)) (π : JointPolicy m S A) (x : Fin S) (hx : x ≠ z) :
    ∑ j ∈ Finset.range (H / 2), (H : ℝ) / 8 *
        ((1 - margProb (π (1 + j) x) istar (θ (x, stepIdx hH (1 + j)))) *
          (lam / (2 * (H : ℝ) ^ 2))) ≤
      gapJ (hardGame istar z hH lam hl hlH cst rest θ) π := by
  set G := hardGame istar z hH lam hl hlH cst rest θ
  have hR : ∀ h s a, G.reward istar h s a ≤ 1 := by
    intro h s a
    simp only [G, hardGame, hardReward, if_true]
    split_ifs <;> linarith
  have hgap := gapJ_ge G π istar hR (piStar istar hH θ) x
  rw [hardGame_value, hardGame_value] at hgap
  simp only [hx, if_false] at hgap
  set ℓs := ellOf istar hH lam θ (deviate π istar (piStar istar hH θ)) x
  set ℓ := ellOf istar hH lam θ π x
  have hℓs : ∀ h, ℓs h = exitQ istar hH lam θ h x (θ (x, stepIdx hH h)) := by
    intro h
    simp only [ℓs, ellOf]
    rw [deviate_sum_coord π istar (piStar istar hH θ) h x (fun b => exitQ istar hH lam θ h x b)]
    simp only [piStar, stayRow]
    simp [ite_mul, Finset.sum_ite_eq']
  have hle : ∀ h, ℓs h ≤ ℓ h := by
    intro h
    have := ellOf_sub_ge (hH := hH) (hl := hl) θ π x h
    rw [hℓs h]
    have h0 : 0 ≤ (1 - margProb (π h x) istar (θ (x, stepIdx hH h))) * (lam / (2 * (H : ℝ) ^ 2)) := by
      have hm : margProb (π h x) istar (θ (x, stepIdx hH h)) ≤ 1 := by
        rw [← sum_margProb (π h x) istar]
        exact Finset.single_le_sum (fun b _ => margProb_nonneg (π h x) istar b) (Finset.mem_univ _)
      exact mul_nonneg (by linarith) (by positivity)
    linarith
  have hchain := chainU_gap_half H hH ℓ ℓs hle (fun h => ellOf_le (hl := hl) (hlH := hlH) θ π x h)
  refine le_trans ?_ (le_trans hchain (by linarith))
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [hℓs]
  exact ellOf_sub_ge (hH := hH) (hl := hl) θ π x (1 + j)

end Hard

end StatisticalRL.Ch7Rest.Marl
