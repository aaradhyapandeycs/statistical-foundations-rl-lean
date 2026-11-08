import Formalization.Ch7Rest.Marl76Restricted

/-!
# Counterexample CE2 to printed Theorem 7.6: the game and the non-causal oracle

Two players, two actions each, horizon `H = 2`, states `Fin S` (`S ≥ 3`): `s₀ = 0`, `s_safe = 1`,
and the `K = S − 2` states `s ≥ 2`.

* Step 1 from `s₀`: if player 1 (index `0`) plays `1` (risky) the next state is uniform over the
  states `≥ 2`, otherwise it is `s_safe`. All other transitions are self-loops.
* Step 2: at `s_safe` both players get `1/2`; at a state `s ≥ 2` both get `1` at the joint action
  `(1,1)` and `0` otherwise (a coordination game). All other rewards are `0`.

The oracle reads `B = supp P̂₁(· | s₀, (1,0))` from the game it is given, coordinates on `(1,1)`
exactly on `B` (and on `(0,0)` elsewhere) at step 2, and at step 1 plays a joint action maximizing
the common continuation payoff. `oracle_isNE`: for every game with these rewards (in particular
every empirical game) the output is a Nash equilibrium (step-1 definition `eq:defn-Nash-E`).
The selection of `B` uses step-1 samples, so the oracle is not causal.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m S H : ℕ} {A : Fin m → ℕ}

theorem pointMass_prob_self {α : Type*} [Fintype α] (x : α) :
    (EnvironmentStage.pointMass x).prob x = 1 := by
  classical
  unfold EnvironmentStage.pointMass
  simp

theorem pointMass_prob_ne {α : Type*} [Fintype α] {x y : α} (h : y ≠ x) :
    (EnvironmentStage.pointMass x).prob y = 0 := by
  classical
  unfold EnvironmentStage.pointMass
  simp [h]

theorem pointMass_expectation {α : Type*} [Fintype α] (x : α) (f : α → ℝ) :
    (EnvironmentStage.pointMass x).expectation f = f x := by
  unfold FiniteDistribution.expectation
  rw [Finset.sum_eq_single x]
  · rw [pointMass_prob_self, one_mul]
  · intro y _ hy; rw [pointMass_prob_ne hy, zero_mul]
  · simp

/-- Expectations under a pure product policy. -/
theorem toJoint_pure_sum (σ : ProductPolicy m S A) (h : ℕ) (s : Fin S) (c : JointAction m A)
    (hc : ∀ j, σ j h s = EnvironmentStage.pointMass (c j)) (g : JointAction m A → ℝ) :
    ∑ a, (toJoint σ h s).prob a * g a = g c := by
  have hp : ∀ a, (toJoint σ h s).prob a = if a = c then 1 else 0 := by
    intro a
    change ∏ j, (σ j h s).prob (a j) = _
    simp only [hc]
    split_ifs with ha
    · subst ha
      exact Finset.prod_eq_one fun j _ => pointMass_prob_self _
    · obtain ⟨j, hj⟩ : ∃ j, a j ≠ c j := by
        by_contra hne; push_neg at hne; exact ha (funext hne)
      exact Finset.prod_eq_zero (Finset.mem_univ j) (pointMass_prob_ne hj)
  simp_rw [hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem deviate_pure_sum (σ : ProductPolicy m S A) (h : ℕ) (s : Fin S) (c : JointAction m A)
    (hc : ∀ j, σ j h s = EnvironmentStage.pointMass (c j)) (i : Fin m)
    (π' : PlayerPolicy S (A i)) (g : JointAction m A → ℝ) :
    ∑ a, (deviate (toJoint σ) i π' h s).prob a * g a =
      ∑ b, (π' h s).prob b * g (Function.update c i b) := by
  rw [deviate_sum]
  have : ∀ a', ∑ b, (toJoint σ h s).prob a' * (π' h s).prob b * g (Function.update a' i b) =
      (toJoint σ h s).prob a' * ∑ b, (π' h s).prob b * g (Function.update a' i b) := by
    intro a'; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
  simp_rw [this]
  exact toJoint_pure_sum σ h s c hc (fun a' => ∑ b, (π' h s).prob b * g (Function.update a' i b))

theorem valueJ_pure_succ (G : MarkovGame m S H A) (σ : ProductPolicy m S A) (i : Fin m) (h k : ℕ)
    (s : Fin S) (c : JointAction m A) (hc : ∀ j, σ j h s = EnvironmentStage.pointMass (c j)) :
    valueJ G (toJoint σ) i h (k + 1) s =
      G.reward i h s c + (G.transition h s c).expectation (valueJ G (toJoint σ) i (h + 1) k) :=
  toJoint_pure_sum σ h s c hc _

theorem valueJ_deviate_pure_succ (G : MarkovGame m S H A) (σ : ProductPolicy m S A) (i : Fin m)
    (π' : PlayerPolicy S (A i)) (h k : ℕ) (s : Fin S) (c : JointAction m A)
    (hc : ∀ j, σ j h s = EnvironmentStage.pointMass (c j)) :
    valueJ G (deviate (toJoint σ) i π') i h (k + 1) s =
      ∑ b, (π' h s).prob b * (G.reward i h s (Function.update c i b) +
        (G.transition h s (Function.update c i b)).expectation
          (valueJ G (deviate (toJoint σ) i π') i (h + 1) k)) :=
  deviate_pure_sum σ h s c hc i π' _

theorem valueJ_zero_fun (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m) (h : ℕ) :
    valueJ G π i h 0 = fun _ => 0 := funext fun _ => rfl

namespace CE2

/-- Two actions per player. -/
abbrev A2 : Fin 2 → ℕ := fun _ => 2

/-- Joint actions of the two players. -/
abbrev JA := JointAction 2 A2

/-- The constant joint action `(b, b)`. -/
def cst (b : Fin 2) : JA := fun _ => b

/-- The joint action `(1, 0)`: player 1 risky, player 2 plays `0`. -/
def a10 : JA := fun j => if (j : ℕ) = 0 then 1 else 0

variable {S : ℕ}

def s0 (hS : 3 ≤ S) : Fin S := ⟨0, by omega⟩
def sSafe (hS : 3 ≤ S) : Fin S := ⟨1, by omega⟩
def t2 (hS : 3 ≤ S) : Fin S := ⟨2, by omega⟩

theorem card_Ici_t2 (hS : 3 ≤ S) : (Finset.Ici (t2 hS)).card = S - 2 := by
  rw [Fin.card_Ici]; rfl

/-- Uniform law on the `S − 2` states `≥ 2`. -/
noncomputable def unifHigh (hS : 3 ≤ S) : FiniteDistribution (Fin S) where
  prob s := if s ∈ Finset.Ici (t2 hS) then 1 / ((S : ℝ) - 2) else 0
  prob_nonneg s := by
    have : (0 : ℝ) < (S : ℝ) - 2 := by
      have : (3 : ℝ) ≤ S := by exact_mod_cast hS
      linarith
    split_ifs <;> positivity
  sum_prob := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, card_Ici_t2, nsmul_eq_mul]
    have h3 : (3 : ℝ) ≤ S := by exact_mod_cast hS
    rw [Nat.cast_sub (by omega)]
    push_cast
    have hne : (S : ℝ) - 2 ≠ 0 := by linarith
    field_simp

/-- The CE2 game. -/
noncomputable def game (hS : 3 ≤ S) : MarkovGame 2 S 2 A2 where
  transition h s a :=
    if h = 1 ∧ s = s0 hS then (if a 0 = 1 then unifHigh hS else EnvironmentStage.pointMass (sSafe hS))
    else EnvironmentStage.pointMass s
  reward _ h s a :=
    if h = 2 then (if s = sSafe hS then 1 / 2 else if t2 hS ≤ s ∧ a = cst 1 then 1 else 0) else 0

theorem game_reward_mem (hS : 3 ≤ S) (i : Fin 2) (h : ℕ) (s : Fin S) (a : JA) :
    0 ≤ (game hS).reward i h s a ∧ (game hS).reward i h s a ≤ 1 := by
  simp only [game]
  split_ifs <;> norm_num

/-- Common continuation payoff at step 2 when coordinating on `(1,1)` exactly on `B`. -/
noncomputable def contW (hS : 3 ≤ S) (B : Finset (Fin S)) (s : Fin S) : ℝ :=
  if s = sSafe hS then 1 / 2 else if t2 hS ≤ s ∧ s ∈ B then 1 else 0

/-- The set `B = supp P̂₁(· | s₀, (1,0))` read from a game. -/
noncomputable def selB (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) : Finset (Fin S) :=
  Finset.univ.filter fun s => 0 < (G'.transition 1 (s0 hS) a10).prob s

/-- The step-1 joint action: a maximizer of the common continuation payoff. -/
noncomputable def stage1 (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (s : Fin S) : JA :=
  Classical.choose (Finite.exists_max fun a : JA =>
    (G'.transition 1 s a).expectation (contW hS (selB hS G')))

theorem stage1_spec (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (s : Fin S) (a : JA) :
    (G'.transition 1 s a).expectation (contW hS (selB hS G')) ≤
      (G'.transition 1 s (stage1 hS G' s)).expectation (contW hS (selB hS G')) :=
  Classical.choose_spec (Finite.exists_max fun a : JA =>
    (G'.transition 1 s a).expectation (contW hS (selB hS G'))) a

/-- The step-2 action of both players at `s`. -/
noncomputable def stage2 (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (s : Fin S) : Fin 2 :=
  if s ∈ selB hS G' then 1 else 0

/-- The non-causal CE2 oracle (a pure product policy). -/
noncomputable def oracle (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) : ProductPolicy 2 S A2 :=
  fun i h s => if h = 2 then EnvironmentStage.pointMass (stage2 hS G' s)
    else EnvironmentStage.pointMass (stage1 hS G' s i)

theorem oracle_two (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (s : Fin S) (j : Fin 2) :
    oracle hS G' j 2 s = EnvironmentStage.pointMass (cst (stage2 hS G' s) j) := by
  simp [oracle, cst]

theorem oracle_one (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (s : Fin S) (j : Fin 2) :
    oracle hS G' j 1 s = EnvironmentStage.pointMass (stage1 hS G' s j) := by
  simp [oracle]

theorem cst_eq_one_iff (b : Fin 2) : cst b = cst 1 ↔ b = 1 := by
  constructor
  · intro h; exact congrFun h 0
  · intro h; rw [h]

theorem reward_two_stage2 (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (i : Fin 2) (s : Fin S) :
    (game hS).reward i 2 s (cst (stage2 hS G' s)) = contW hS (selB hS G') s := by
  simp only [game, contW, stage2, if_true]
  by_cases hs : s ∈ selB hS G'
  · simp [hs]
  · have : cst (0 : Fin 2) ≠ cst 1 := fun h => by
      have := congrFun h 0; simp [cst] at this
    simp [hs, this]

/-- The step-2 profile is a stage Nash equilibrium for every `B`. -/
theorem reward_two_update_le (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2) (i : Fin 2) (s : Fin S)
    (b : Fin 2) :
    (game hS).reward i 2 s (Function.update (cst (stage2 hS G' s)) i b) ≤
      contW hS (selB hS G') s := by
  rw [← reward_two_stage2 hS G' i s]
  simp only [game, if_true]
  by_cases h1 : s = sSafe hS
  · simp [h1]
  · by_cases h2 : t2 hS ≤ s ∧ Function.update (cst (stage2 hS G' s)) i b = cst 1
    · have h3 : t2 hS ≤ s ∧ cst (stage2 hS G' s) = cst 1 := by
        refine ⟨h2.1, ?_⟩
        let j : Fin 2 := if i = 0 then 1 else 0
        have hj : j ≠ i := by fin_cases i <;> simp [j]
        have h := congrFun h2.2 j
        rw [Function.update_of_ne hj] at h
        simp only [cst] at h ⊢
        rw [h]
      rw [if_neg h1, if_neg h1, if_pos h2, if_pos h3]
    · simp only [h1, h2, if_false]
      split_ifs <;> norm_num

/-- For every game with the CE2 rewards, the oracle output is a Nash equilibrium. -/
theorem oracle_isNE (hS : 3 ≤ S) (G' : MarkovGame 2 S 2 A2)
    (hrew : G'.reward = (game hS).reward) : IsNE G' (oracle hS G') := by
  intro s i
  set σ := oracle hS G'
  set W := contW hS (selB hS G')
  -- values at step 2
  have hV2 : valueJ G' (toJoint σ) i 2 1 = W := by
    funext s'
    rw [valueJ_pure_succ G' σ i 2 0 s' (cst (stage2 hS G' s')) (oracle_two hS G' s'), hrew,
      reward_two_stage2, valueJ_zero_fun, FiniteDistribution.expectation_const, add_zero]
  have hD2 : ∀ π' : PlayerPolicy S (A2 i), ∀ s',
      valueJ G' (deviate (toJoint σ) i π') i 2 1 s' ≤ W s' := by
    intro π' s'
    rw [valueJ_deviate_pure_succ G' σ i π' 2 0 s' (cst (stage2 hS G' s')) (oracle_two hS G' s')]
    rw [valueJ_zero_fun]
    simp only [FiniteDistribution.expectation_const, add_zero, hrew]
    calc ∑ b, (π' 2 s').prob b * (game hS).reward i 2 s' (Function.update (cst (stage2 hS G' s')) i b)
        ≤ ∑ b, (π' 2 s').prob b * W s' := Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (reward_two_update_le hS G' i s' b) ((π' 2 s').prob_nonneg b)
      _ = W s' := by rw [← Finset.sum_mul, (π' 2 s').sum_prob, one_mul]
  have hr1 : ∀ a, G'.reward i 1 s a = 0 := by intro a; rw [hrew]; simp [game]
  have hV1 : valueJ G' (toJoint σ) i 1 2 s =
      (G'.transition 1 s (stage1 hS G' s)).expectation W := by
    rw [valueJ_pure_succ G' σ i 1 1 s (stage1 hS G' s) (oracle_one hS G' s), hr1, zero_add, hV2]
  have hdev : ∀ π' : PlayerPolicy S (A2 i),
      valueJ G' (deviate (toJoint σ) i π') i 1 2 s ≤ valueJ G' (toJoint σ) i 1 2 s := by
    intro π'
    rw [valueJ_deviate_pure_succ G' σ i π' 1 1 s (stage1 hS G' s) (oracle_one hS G' s), hV1]
    calc ∑ b, (π' 1 s).prob b * (G'.reward i 1 s (Function.update (stage1 hS G' s) i b) +
          (G'.transition 1 s (Function.update (stage1 hS G' s) i b)).expectation
            (valueJ G' (deviate (toJoint σ) i π') i 2 1))
        ≤ ∑ b, (π' 1 s).prob b * (G'.transition 1 s (stage1 hS G' s)).expectation W := by
          refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ ((π' 1 s).prob_nonneg b)
          rw [hr1, zero_add]
          exact (FiniteDistribution.expectation_mono _ (hD2 π')).trans (stage1_spec hS G' s _)
      _ = _ := by rw [← Finset.sum_mul, (π' 1 s).sum_prob, one_mul]
  rw [← valueJ_toJoint, ← bestResponseValueJ_toJoint]
  apply le_antisymm
  · have h := valueJ_deviate_le_bestResponseValueJ G' (toJoint σ) i (σ i) s
    have heq : valueJ G' (deviate (toJoint σ) i (σ i)) i 1 2 s = valueJ G' (toJoint σ) i 1 2 s := by
      rw [valueJ_congr G' _ _ i (deviate_toJoint_sum σ i (σ i)) 2 1 s, Function.update_eq_self]
    rwa [heq] at h
  · unfold bestResponseValueJ
    haveI : Nonempty (PlayerPolicy S (A2 i)) := ⟨σ i⟩
    exact ciSup_le hdev

end CE2

end StatisticalRL.Ch7Rest.Marl76
