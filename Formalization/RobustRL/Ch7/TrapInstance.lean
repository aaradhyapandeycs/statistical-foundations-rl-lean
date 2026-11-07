import Formalization.RobustRL.Ch7.Ch7Definitions
import Formalization.MDP.ForcedPrefixBridge
import Formalization.MDP.FiniteOptimal
import Formalization.ModelFree.QLearningRobustComparator

/-!
# The deterministic horizon-trap RMDP (SOURCE-ISSUES C37)

States `Fin (L+3)`: `0 = s₀`, `1,…,L` = chain `c₁…c_L`, `L+1 = g` (absorbing,
reward 1), `L+2 = d` (absorbing, reward 0). Actions `Fin 2`. At `s₀`, action `0`
enters the chain (reward 0) and action `1` bails to `d` with reward `1/2`;
every other state ignores the action. The nominal kernel is deterministic.

This file proves, without any robust Bellman or fixed-point theory:
* DRVI from `Q̂₀ = 0` on (any model with) this deterministic kernel, for any
  row-ball family containing its centre, has `Q̂_T(s₀,0) ≤ 0 < 1/2 ≤ Q̂_T(s₀,1)`
  for `1 ≤ T ≤ L+1`, so every greedy selector bails at `s₀`;
* for every ball family whose balls around a point mass `δ_j` only contain rows
  with mass `≥ 1-σ` at `j` (TV: half-L1; χ²: support condition), the robust
  value of "always action 0" at `s₀` is `≥ q^{L+1}/(1-q)`, `q = γ(1-σ)`;
* the robust value at `s₀` of any policy bailing at `s₀` is `≤ 1/2`.
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.HorizonTrap

open StatisticalRL.EnvironmentStage

section Balls

variable {State : Type*} [Fintype State]

theorem fd_ext {p q : FiniteDistribution State} (h : ∀ x, p.prob x = q.prob x) : p = q := by
  cases p with
  | mk pp _ _ =>
    cases q with
    | mk qq _ _ =>
      have : pp = qq := funext h
      subst this
      rfl

theorem pointMass_prob [DecidableEq State] (j x : State) :
    (pointMass j).prob x = if x = j then 1 else 0 := by
  by_cases h : x = j <;> simp [pointMass, h]

/-- A row-ball family is a *trap ball* at radius `σ` when it contains its centre
and every row in the ball around a point mass `δ_j` keeps mass `≥ 1-σ` at `j`. -/
structure TrapBall (ball : RowBall State) (σ : ℝ) : Prop where
  self_mem : ∀ p, p ∈ ball p σ
  pointMass_mass : ∀ (j : State) (q : FiniteDistribution State),
    q ∈ ball (pointMass j) σ → 1 - σ ≤ q.prob j

theorem tvBall_trapBall {σ : ℝ} (hσ : 0 ≤ σ) : TrapBall (tvBall (State := State)) σ := by
  classical
  constructor
  · intro p
    show (1 / 2 : ℝ) * ∑ x, |p.prob x - p.prob x| ≤ σ
    simp [hσ]
  · intro j q hq
    change (1 / 2 : ℝ) * ∑ x, |(pointMass j).prob x - q.prob x| ≤ σ at hq
    have hterm : ∀ x, q.prob x + (if x = j then 1 - 2 * q.prob x else 0) ≤
        |(pointMass j).prob x - q.prob x| := by
      intro x
      rw [pointMass_prob]
      by_cases hx : x = j
      · simp only [hx, if_true]
        have := le_abs_self (1 - q.prob j)
        linarith
      · simp only [hx, if_false]
        rw [zero_sub, abs_neg, abs_of_nonneg (q.prob_nonneg x)]
        linarith
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦ hterm x)
    rw [Finset.sum_add_distrib, q.sum_prob, Finset.sum_ite_eq' Finset.univ j] at hsum
    simp only [Finset.mem_univ, if_true] at hsum
    linarith

theorem chiBall_pointMass_eq {σ : ℝ} (j : State) (q : FiniteDistribution State)
    (hq : q ∈ chiBall (pointMass j) σ) : q.prob j = 1 := by
  classical
  have hzero : ∀ x, x ≠ j → q.prob x = 0 := by
    intro x hx
    apply hq.1 x
    rw [pointMass_prob, if_neg hx]
  have := q.sum_prob
  rw [Finset.sum_eq_single j (fun x _ hx ↦ hzero x hx) (by simp)] at this
  exact this

theorem chiBall_trapBall {σ : ℝ} (hσ : 0 ≤ σ) : TrapBall (chiBall (State := State)) σ := by
  constructor
  · intro p
    exact QLearning.qChiBall_self p σ hσ
  · intro j q hq
    rw [chiBall_pointMass_eq j q hq]
    linarith

end Balls

section Generic

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- For nonnegative `V`, the exact robust row infimum lies in `[0, ⟨p, V⟩]`. -/
theorem rowRobustInf_bounds {ball : RowBall State} {σ : ℝ} (hb : ∀ p, p ∈ ball p σ)
    (p : FiniteDistribution State) {V : State → ℝ} (hV : ∀ x, 0 ≤ V x) :
    0 ≤ rowRobustInf ball p σ V ∧ rowRobustInf ball p σ V ≤ p.expectation V := by
  have hmem : p.expectation V ∈
      (fun q : FiniteDistribution State ↦ q.expectation V) '' ball p σ := ⟨p, hb p, rfl⟩
  constructor
  · apply le_csInf ⟨_, hmem⟩
    rintro _ ⟨q, -, rfl⟩
    exact q.expectation_nonneg hV
  · apply csInf_le _ hmem
    refine ⟨0, ?_⟩
    rintro _ ⟨q, -, rfl⟩
    exact q.expectation_nonneg hV

theorem actionMaximum_nonneg' [Nonempty Action] {f : Action → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ actionMaximum f :=
  (h (Classical.arbitrary Action)).trans (le_actionMaximum f _)

theorem actionMaximum_nonpos' [Nonempty Action] {f : Action → ℝ} (h : ∀ a, f a ≤ 0) :
    actionMaximum f ≤ 0 :=
  (Finset.sup'_le_iff Finset.univ_nonempty f).2 fun a _ ↦ h a

/-- DRVI iterates from `Q̂₀ = 0` are nonnegative. -/
theorem drviIterate_nonneg {ball : RowBall State} {σ : ℝ} (hb : ∀ p, p ∈ ball p σ)
    (M : DiscountedMDP State Action) : ∀ t s a, 0 ≤ drviIterate ball M σ t s a := by
  letI : Nonempty Action := M.action_nonempty
  intro t
  induction t with
  | zero => intro s a; simp [drviIterate]
  | succ t ih =>
    intro s a
    simp only [drviIterate, robustBellman]
    have hV : ∀ x, 0 ≤ actionMaximum (drviIterate ball M σ t x) :=
      fun x ↦ actionMaximum_nonneg' (ih x)
    have := (rowRobustInf_bounds hb (M.transition s a) hV).1
    exact add_nonneg (M.reward_nonneg s a) (mul_nonneg M.discount_nonneg this)

/-- Policy-transition expectation for a deterministic policy. -/
theorem policyTransition_detPolicy_expectation (M : DiscountedMDP State Action)
    (f : State → Action) (s : State) (W : State → ℝ) :
    (M.policyTransition (detPolicy f) s).expectation W = (M.transition s (f s)).expectation W := by
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [DiscountedMDP.policyTransition_prob]
  simp only [detPolicy]
  rw [expectation_pointMass]

/-- Bellman equation of the actual trajectory value for a deterministic policy. -/
theorem trajectoryValue_detPolicy_bellman (M : DiscountedMDP State Action)
    (f : State → Action) (s : State) :
    M.trajectoryExpectedValue (detPolicy f) s =
      M.reward s (f s) + M.discount *
        (M.transition s (f s)).expectation (M.trajectoryExpectedValue (detPolicy f)) := by
  rw [M.trajectoryExpectedValue_eq_valueFixedPoint]
  have h := congrFun (M.valueFixedPoint_spec (detPolicy f)) s
  rw [← h]
  simp only [DiscountedMDP.valueBellman, policyTransition_detPolicy_expectation]
  congr 1
  simp [detPolicy, expectation_pointMass]

end Generic

/-! ## The trap instance -/

variable (L : ℕ)

/-- Deterministic successor of the trap. -/
def next (s : Fin (L + 3)) (a : Fin 2) : Fin (L + 3) :=
  if s.val = 0 then (if a.val = 0 then ⟨1, by omega⟩ else ⟨L + 2, by omega⟩)
  else if h : s.val ≤ L then ⟨s.val + 1, by omega⟩ else s

/-- Reward: `1` at `g = L+1`, `1/2` for bailing at `s₀`, `0` otherwise. -/
noncomputable def reward (s : Fin (L + 3)) (a : Fin 2) : ℝ :=
  if s.val = L + 1 then 1 else if s.val = 0 ∧ a.val = 1 then 1 / 2 else 0

theorem reward_nonneg (s : Fin (L + 3)) (a : Fin 2) : 0 ≤ reward L s a := by
  unfold reward; split_ifs <;> norm_num

theorem reward_le_one (s : Fin (L + 3)) (a : Fin 2) : reward L s a ≤ 1 := by
  unfold reward; split_ifs <;> norm_num

/-- The nominal trap MDP with discount `γ`. -/
noncomputable def trapMDP (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    DiscountedMDP (Fin (L + 3)) (Fin 2) where
  state_nonempty := ⟨0⟩
  action_nonempty := ⟨0⟩
  transition s a := pointMass (next L s a)
  reward := reward L
  reward_nonneg := reward_nonneg L
  reward_le_one := reward_le_one L
  discount := γ
  discount_nonneg := hγ0
  discount_lt_one := hγ1

section DRVI

variable {L}
variable {ball : RowBall (Fin (L + 3))} {σ : ℝ}
variable (M : DiscountedMDP (Fin (L + 3)) (Fin 2))

/-- Along the chain, `Q̂_t(c_k, ·) ≤ 0` whenever `k + t ≤ L + 1`. -/
theorem drvi_chain_nonpos (hb : ∀ p, p ∈ ball p σ)
    (hT : ∀ s a, M.transition s a = pointMass (next L s a))
    (hr : ∀ s a, M.reward s a = reward L s a) :
    ∀ t (s : Fin (L + 3)), 1 ≤ s.val → s.val + t ≤ L + 1 →
      ∀ a, drviIterate ball M σ t s a ≤ 0 := by
  letI : Nonempty (Fin 2) := ⟨0⟩
  intro t
  induction t with
  | zero => intro s _ _ a; simp [drviIterate]
  | succ t ih =>
    intro s hs hst a
    have hsL : s.val ≤ L := by omega
    have hnext : next L s a = ⟨s.val + 1, by omega⟩ := by
      unfold next; rw [if_neg (by omega), dif_pos hsL]
    have hrew : M.reward s a = 0 := by
      rw [hr]; unfold reward; rw [if_neg (by omega), if_neg (by omega)]
    simp only [drviIterate, robustBellman, hrew, zero_add, hT, hnext]
    have hnn : ∀ x, 0 ≤ actionMaximum (drviIterate ball M σ t x) :=
      fun x ↦ actionMaximum_nonneg' (drviIterate_nonneg hb M t x)
    have hup := (rowRobustInf_bounds hb (pointMass (⟨s.val + 1, by omega⟩ : Fin (L + 3))) hnn).2
    rw [expectation_pointMass] at hup
    have hnp : actionMaximum (drviIterate ball M σ t ⟨s.val + 1, by omega⟩) ≤ 0 :=
      actionMaximum_nonpos' (ih ⟨s.val + 1, by omega⟩ (by simp) (by simp; omega))
    exact mul_nonpos_of_nonneg_of_nonpos M.discount_nonneg (hup.trans hnp)

/-- At `s₀`, entering the chain has `Q̂_T(s₀,0) ≤ 0` for `1 ≤ T ≤ L+1`. -/
theorem drvi_enter_nonpos (hb : ∀ p, p ∈ ball p σ)
    (hT : ∀ s a, M.transition s a = pointMass (next L s a))
    (hr : ∀ s a, M.reward s a = reward L s a) (t : ℕ) (ht : t ≤ L) :
    drviIterate ball M σ (t + 1) 0 0 ≤ 0 := by
  letI : Nonempty (Fin 2) := ⟨0⟩
  have hnext : next L 0 0 = ⟨1, by omega⟩ := by unfold next; simp
  have hrew : M.reward 0 0 = 0 := by
    rw [hr]; unfold reward; simp
  simp only [drviIterate, robustBellman, hrew, zero_add, hT, hnext]
  have hnn : ∀ x, 0 ≤ actionMaximum (drviIterate ball M σ t x) :=
    fun x ↦ actionMaximum_nonneg' (drviIterate_nonneg hb M t x)
  have hup := (rowRobustInf_bounds hb (pointMass (⟨1, by omega⟩ : Fin (L + 3))) hnn).2
  rw [expectation_pointMass] at hup
  have hnp : actionMaximum (drviIterate ball M σ t ⟨1, by omega⟩) ≤ 0 :=
    actionMaximum_nonpos' (drvi_chain_nonpos M hb hT hr t ⟨1, by omega⟩ (by simp) (by simp; omega))
  exact mul_nonpos_of_nonneg_of_nonpos M.discount_nonneg (hup.trans hnp)

/-- At `s₀`, bailing has `Q̂_{t+1}(s₀,1) ≥ 1/2`. -/
theorem drvi_bail_ge (hb : ∀ p, p ∈ ball p σ)
    (hr : ∀ s a, M.reward s a = reward L s a) (t : ℕ) :
    1 / 2 ≤ drviIterate ball M σ (t + 1) 0 1 := by
  letI : Nonempty (Fin 2) := ⟨0⟩
  have hrew : M.reward 0 1 = 1 / 2 := by
    rw [hr]; unfold reward; simp
  simp only [drviIterate, robustBellman, hrew]
  have hnn : ∀ x, 0 ≤ actionMaximum (drviIterate ball M σ t x) :=
    fun x ↦ actionMaximum_nonneg' (drviIterate_nonneg hb M t x)
  have := (rowRobustInf_bounds hb (M.transition 0 1) hnn).1
  have := mul_nonneg M.discount_nonneg this
  linarith

/-- Every greedy selector of `Q̂_T`, `1 ≤ T ≤ L+1`, bails at `s₀`. -/
theorem drvi_greedy_bails (hb : ∀ p, p ∈ ball p σ)
    (hT : ∀ s a, M.transition s a = pointMass (next L s a))
    (hr : ∀ s a, M.reward s a = reward L s a) (T : ℕ) (hT1 : 1 ≤ T) (hTL : T ≤ L + 1)
    (f : Fin (L + 3) → Fin 2) (hf : IsGreedy (drviIterate ball M σ T) f) : f 0 = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have h0 := drvi_enter_nonpos M hb hT hr t (by omega)
  have h1 := drvi_bail_ge M hb hr t
  have hg := hf 0 1
  by_contra hne
  have hf0 : f 0 = 0 := by omega
  rw [hf0] at hg
  linarith

end DRVI

section Values

variable {L}

/-- Lower bound for "always enter": for every kernel keeping mass `≥ 1-σ` on the
trap successor of action `0`, `V^{π₀,K}(s₀) ≥ q^{L+1}/(1-q)`, `q = γ(1-σ)`. -/
theorem enterValue_lower (M : DiscountedMDP (Fin (L + 3)) (Fin 2))
    (hr : ∀ s a, M.reward s a = reward L s a) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hmass : ∀ s, 1 - σ ≤ (M.transition s 0).prob (next L s 0)) :
    (M.discount * (1 - σ)) ^ (L + 1) / (1 - M.discount * (1 - σ)) ≤
      M.trajectoryExpectedValue (detPolicy fun _ ↦ 0) 0 := by
  set V := M.trajectoryExpectedValue (detPolicy fun _ ↦ (0 : Fin 2)) with hVdef
  set q := M.discount * (1 - σ) with hq
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hq0 : 0 ≤ q := mul_nonneg hγ0 (by linarith)
  have hq1 : q < 1 := by
    have : q ≤ M.discount := by nlinarith
    linarith
  have hVnn : ∀ s, 0 ≤ V s := fun s ↦ (M.trajectoryExpectedValue_bounds _ s).1
  -- one-step lower bound
  have hstep : ∀ s, M.reward s 0 + q * V (next L s 0) ≤ V s := by
    intro s
    have hb := trajectoryValue_detPolicy_bellman M (fun _ ↦ (0 : Fin 2)) s
    rw [← hVdef] at hb
    rw [hb]
    have hsingle : (M.transition s 0).prob (next L s 0) * V (next L s 0) ≤
        (M.transition s 0).expectation V := by
      unfold FiniteDistribution.expectation
      exact Finset.single_le_sum (f := fun x ↦ (M.transition s 0).prob x * V x)
        (fun x _ ↦ mul_nonneg ((M.transition s 0).prob_nonneg x) (hVnn x))
        (Finset.mem_univ _)
    have hm : (1 - σ) * V (next L s 0) ≤
        (M.transition s 0).prob (next L s 0) * V (next L s 0) :=
      mul_le_mul_of_nonneg_right (hmass s) (hVnn _)
    have : q * V (next L s 0) ≤ M.discount * (M.transition s 0).expectation V := by
      rw [hq, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hm.trans hsingle) hγ0
    linarith
  -- the goal state
  let g : Fin (L + 3) := ⟨L + 1, by omega⟩
  have hg : 1 / (1 - q) ≤ V g := by
    have h := hstep g
    have hn : next L g 0 = g := by
      unfold next; rw [if_neg (by simp [g]), dif_neg (by simp [g])]
    have hrg : M.reward g 0 = 1 := by rw [hr]; unfold reward; simp [g]
    rw [hn, hrg] at h
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- along the chain
  have hchain : ∀ j, j ≤ L + 1 → q ^ j * V g ≤ V ⟨L + 1 - j, by omega⟩ := by
    intro j
    induction j with
    | zero => intro _; simp [g]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      set k : Fin (L + 3) := ⟨L + 1 - (j + 1), by omega⟩
      have hk : k.val ≤ L := by simp only [k]; omega
      have hn : next L k 0 = ⟨L + 1 - j, by omega⟩ := by
        unfold next
        by_cases h0 : k.val = 0
        · rw [if_pos h0]; simp only [Fin.isValue, Fin.val_zero, if_true]
          ext; simp [k] at h0 ⊢; try omega
        · rw [if_neg h0, dif_pos hk]; ext; simp [k]; omega
      have hrk : M.reward k 0 = 0 := by
        rw [hr]; unfold reward; rw [if_neg (by omega)]; simp
      have h := hstep k
      rw [hn, hrk, zero_add] at h
      calc q ^ (j + 1) * V g = q * (q ^ j * V g) := by ring
        _ ≤ q * V ⟨L + 1 - j, by omega⟩ := mul_le_mul_of_nonneg_left ih' hq0
        _ ≤ V k := h
  have h0 := hchain (L + 1) le_rfl
  have hfin : (⟨L + 1 - (L + 1), by omega⟩ : Fin (L + 3)) = 0 := by ext; simp
  rw [hfin] at h0
  calc q ^ (L + 1) / (1 - q) = q ^ (L + 1) * (1 / (1 - q)) := by ring
    _ ≤ q ^ (L + 1) * V g := mul_le_mul_of_nonneg_left hg (pow_nonneg hq0 _)
    _ ≤ V 0 := h0

/-- Any deterministic policy bailing at `s₀` has nominal value exactly `1/2` at `s₀`. -/
theorem bailValue_eq (M : DiscountedMDP (Fin (L + 3)) (Fin 2))
    (hT : ∀ s a, M.transition s a = pointMass (next L s a))
    (hr : ∀ s a, M.reward s a = reward L s a)
    (f : Fin (L + 3) → Fin 2) (hf : f 0 = 1) :
    M.trajectoryExpectedValue (detPolicy f) 0 = 1 / 2 := by
  set V := M.trajectoryExpectedValue (detPolicy f) with hVdef
  let d : Fin (L + 3) := ⟨L + 2, by omega⟩
  have hd : V d = 0 := by
    have hb := trajectoryValue_detPolicy_bellman M f d
    rw [← hVdef, hT, expectation_pointMass] at hb
    have hn : next L d (f d) = d := by
      unfold next; rw [if_neg (by simp [d]), dif_neg (by simp [d])]
    have hrd : M.reward d (f d) = 0 := by
      rw [hr]; unfold reward; rw [if_neg (by simp [d]), if_neg (by simp [d])]
    rw [hn, hrd, zero_add] at hb
    have hγ1 := M.discount_lt_one
    have : (1 - M.discount) * V d = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hb := trajectoryValue_detPolicy_bellman M f 0
  rw [← hVdef, hT, expectation_pointMass, hf] at hb
  have hn : next L 0 1 = d := by unfold next; simp [d]
  have hr0 : M.reward 0 1 = 1 / 2 := by rw [hr]; unfold reward; simp
  rw [hn, hr0, hd, mul_zero, add_zero] at hb
  exact hb

end Values

end StatisticalRL.RobustRL.Ch7.HorizonTrap
