import Formalization.Ch7Rest.Marl76BestResponse

/-!
# Best responses at every step, and NE ⇒ CCE with the converse failing

Source: `chapters/marl.tex`. Markov policies :71–91, values `eq:value-function-defn` :96–106,
best-response value `eq:defn-optimal-V` :119–126, existence of a best response attaining it at every
`(s, h)` :128–132, Bellman optimality for agent `i` with terminal value `0` :135–143, NE
`eq:defn-Nash-E` :213–221, CCE `eq:defn-CCE` :232–238, "every Nash equilibrium is also a CCE,
although the converse does not generally hold" :240.

* `starValue G π i h s = ⨆ π', V^{π'_i × π_{-i}}_{i,h}(s)`: the step-`h` best-response value
  (`eq:defn-optimal-V`), a real `iSup` over all Markov policies of agent `i`, with `π_{-i}` the
  marginal of the joint policy `π` (`deviate`).
* `starValue_eq_brW`: it equals the backward recursion `brW` at every `h ∈ [1, H + 1]`.
* `valueJ_deviate_le_starValue`: the supremum dominates every deviation (it is a genuine supremum,
  not a junk value).
* `valueJ_brPolicy_eq_starValue`: the greedy best response `brPolicy` attains `starValue` at all
  `(s, h)` simultaneously.
* `starValue_bellman`, `starValue_terminal`: the Bellman optimality equation and `V⋆_{H+1} = 0`.
* `isCCE_of_isNE_of_prob_eq`: a joint policy equal to the product law of an NE is a CCE;
  `isNE_iff_isCCE_toJoint`: for product policies NE and CCE coincide.
* `coordGame`, `coordPolicy`: a two-player, one-state, one-step coordination game and the correlated
  policy uniform on `{(0,0), (1,1)}`; `coordPolicy_isCCE`: it is a CCE;
  `coordPolicy_not_product`: its step-1 law is not a product law, so it is not (the joint law of) an
  NE.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m S H : ℕ} {A : Fin m → ℕ}

/-! ### Best-response values at every step -/

/-- The step-`h` best-response value `V^{⋆,π_{-i}}_{i,h}(s)` (`marl.tex:122–125`): the supremum over
Markov policies `π'` of agent `i` of the value from step `h` to `H` of `π'_i × π_{-i}`. -/
noncomputable def starValue (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (h : ℕ) (s : Fin S) : ℝ :=
  ⨆ π' : PlayerPolicy S (A i), valueJ G (deviate π i π') i h (H + 1 - h) s

theorem starValue_eq_brW (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) (h : ℕ) (hh : h ≤ H + 1) (s : Fin S) :
    starValue G π i h s = brW G π i h (H + 1 - h) s := by
  have hatt := congrFun (valueJ_brPolicy G π i hAi (H + 1 - h) h (by omega)) s
  unfold starValue
  apply le_antisymm
  · haveI : Nonempty (PlayerPolicy S (A i)) := ⟨brPolicy G π i hAi⟩
    exact ciSup_le fun π' => valueJ_deviate_le_brW G π i π' (H + 1 - h) h s
  · rw [← hatt]
    refine le_ciSup (f := fun π' : PlayerPolicy S (A i) =>
      valueJ G (deviate π i π') i h (H + 1 - h) s) ⟨brW G π i h (H + 1 - h) s, ?_⟩
      (brPolicy G π i hAi)
    rintro _ ⟨π', rfl⟩
    exact valueJ_deviate_le_brW G π i π' (H + 1 - h) h s

/-- Every deviation is dominated by the best-response value (no junk `iSup`). -/
theorem valueJ_deviate_le_starValue (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (π' : PlayerPolicy S (A i)) (h : ℕ) (s : Fin S) :
    valueJ G (deviate π i π') i h (H + 1 - h) s ≤ starValue G π i h s :=
  le_ciSup (f := fun π' : PlayerPolicy S (A i) => valueJ G (deviate π i π') i h (H + 1 - h) s)
    ⟨brW G π i h (H + 1 - h) s, by
      rintro _ ⟨π'', rfl⟩; exact valueJ_deviate_le_brW G π i π'' (H + 1 - h) h s⟩ π'

/-- The greedy best response attains the best-response value at every `(s, h)`, `h ≤ H + 1`
(`marl.tex:128–132`). -/
theorem valueJ_brPolicy_eq_starValue (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) (h : ℕ) (hh : h ≤ H + 1) (s : Fin S) :
    valueJ G (deviate π i (brPolicy G π i hAi)) i h (H + 1 - h) s = starValue G π i h s := by
  rw [starValue_eq_brW G π i hAi h hh,
    congrFun (valueJ_brPolicy G π i hAi (H + 1 - h) h (by omega)) s]

/-- Terminal value `V^{⋆,π_{-i}}_{i,H+1} = 0` (`marl.tex:143`). -/
theorem starValue_terminal (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) (s : Fin S) : starValue G π i (H + 1) s = 0 := by
  rw [starValue_eq_brW G π i hAi (H + 1) le_rfl, Nat.sub_self]
  rfl

/-- Bellman optimality for agent `i` against `π_{-i}` (`marl.tex:135–143`): for `h ∈ [1, H]`,
`V⋆_h(s) = max_b E_{a ∼ π_h(·|s)}[r_{i,h}(s, a_{-i}, b) + ⟨P_h(·|s, a_{-i}, b), V⋆_{h+1}⟩]`. -/
theorem starValue_bellman (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hAi : 0 < A i) (h : ℕ) (hh : h ≤ H) (s : Fin S) :
    starValue G π i h s = ⨆ b : Fin (A i), ∑ a', (π h s).prob a' *
      (G.reward i h s (Function.update a' i b) +
        (G.transition h s (Function.update a' i b)).expectation (starValue G π i (h + 1))) := by
  have hnext : starValue G π i (h + 1) = brW G π i (h + 1) (H - h) := by
    funext s'
    rw [starValue_eq_brW G π i hAi (h + 1) (by omega)]
    congr 1
    omega
  rw [starValue_eq_brW G π i hAi h (by omega), hnext]
  have hk : H + 1 - h = (H - h) + 1 := by omega
  rw [hk]
  rfl

/-! ### NE ⇒ CCE, and the converse fails -/

/-- A joint policy whose laws are the product laws of a Nash equilibrium is a CCE
(`marl.tex:240`). -/
theorem isCCE_of_isNE_of_prob_eq (G : MarkovGame m S H A) (σ : ProductPolicy m S A)
    (π : JointPolicy m S A) (hπ : ∀ h s a, (π h s).prob a = jointProb σ h s a)
    (hNE : IsNE G σ) : IsCCE G π := by
  have : π = toJoint σ := by
    funext h s
    have hp : ∀ a, (π h s).prob a = (toJoint σ h s).prob a := fun a => hπ h s a
    cases h1 : π h s
    cases h2 : toJoint σ h s
    rw [h1, h2] at hp
    simp only [FiniteDistribution.mk.injEq]
    exact funext hp
  rw [this]
  exact hNE.isCCE

/-- The value of a product policy is at most its best-response value (deviate to `σ_i` itself). -/
theorem value_le_bestResponseValue (G : MarkovGame m S H A) (σ : ProductPolicy m S A) (i : Fin m)
    (s : Fin S) : value G σ i 1 H s ≤ bestResponseValue G σ i s := by
  rw [← bestResponseValueJ_toJoint, ← valueJ_toJoint]
  have h := valueJ_deviate_le_bestResponseValueJ G (toJoint σ) i (σ i) s
  rwa [valueJ_congr G _ _ i (deviate_toJoint_sum σ i (σ i)) H 1 s, Function.update_eq_self] at h

/-- For product policies, CCE and NE coincide. -/
theorem isNE_iff_isCCE_toJoint (G : MarkovGame m S H A) (σ : ProductPolicy m S A) :
    IsNE G σ ↔ IsCCE G (toJoint σ) := by
  refine ⟨fun h => h.isCCE, fun h s i => ?_⟩
  have h1 := h s i
  rw [bestResponseValueJ_toJoint, valueJ_toJoint] at h1
  exact le_antisymm (value_le_bestResponseValue G σ i s) h1

/-- Action profiles of the two-player game with two actions each. -/
abbrev CoordAction := (i : Fin 2) → Fin ((fun _ : Fin 2 => 2) i)

/-- The two-player, one-state, one-step coordination game: both players get reward `1` when their
actions agree and `0` otherwise; the only state is absorbing. -/
noncomputable def coordGame : MarkovGame 2 1 1 (fun _ => 2) where
  transition _ _ _ := EnvironmentStage.pointMass 0
  reward _ _ _ a := if a 0 = a 1 then 1 else 0

theorem sum_coordAction (f : CoordAction → ℝ) :
    ∑ a, f a = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  have hs := Fintype.sum_equiv (finTwoArrowEquiv (Fin 2)) (f : (Fin 2 → Fin 2) → ℝ)
    (fun p => f ![p.1, p.2]) (fun a => congrArg f (by funext j; fin_cases j <;> rfl))
  rw [show (∑ a : CoordAction, f a) = ∑ a : Fin 2 → Fin 2, f a from rfl, hs,
    Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  ring

/-- The correlated policy uniform on `{(0,0), (1,1)}`. -/
noncomputable def coordPolicy : JointPolicy 2 1 (fun _ => 2) := fun _ _ =>
  { prob := fun a => if a 0 = a 1 then 1 / 2 else 0
    prob_nonneg := fun a => by split_ifs <;> norm_num
    sum_prob := by
      rw [sum_coordAction]
      simp
      norm_num }

theorem coordGame_reward_mem (i : Fin 2) (h : ℕ) (s : Fin 1) (a : CoordAction) :
    0 ≤ coordGame.reward i h s a ∧ coordGame.reward i h s a ≤ 1 := by
  simp only [coordGame]
  split_ifs <;> norm_num

/-- `coordPolicy` is a CCE of `coordGame`: its value `1` is the largest possible value. -/
theorem coordPolicy_isCCE : IsCCE coordGame coordPolicy := by
  have hle : ∀ (π : JointPolicy 2 1 (fun _ => 2)) (i : Fin 2) (s : Fin 1),
      valueJ coordGame π i 1 1 s ≤ 1 := by
    intro π i s
    simp only [valueJ, FiniteDistribution.expectation, mul_zero, Finset.sum_const_zero, add_zero]
    calc ∑ a, (π 1 s).prob a * coordGame.reward i 1 s a ≤ ∑ a, (π 1 s).prob a * 1 :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (coordGame_reward_mem i 1 s a).2 ((π 1 s).prob_nonneg a)
      _ = 1 := by simp [(π 1 s).sum_prob]
  intro s i
  have hv : valueJ coordGame coordPolicy i 1 1 s = 1 := by
    simp only [valueJ, FiniteDistribution.expectation, mul_zero, Finset.sum_const_zero, add_zero]
    rw [sum_coordAction]
    simp [coordPolicy, coordGame]
    norm_num
  rw [hv]
  unfold bestResponseValueJ
  haveI : Nonempty (PlayerPolicy 1 ((fun _ : Fin 2 => 2) i)) :=
    ⟨fun _ _ => EnvironmentStage.pointMass 0⟩
  exact ciSup_le fun π' => hle _ i s

/-- The step-1 law of `coordPolicy` is not a product law: `p q = 1/2`, `p q' = 0` and
`p' q' = 1/2` are incompatible. -/
theorem coordPolicy_not_product (σ : ProductPolicy 2 1 (fun _ => 2)) :
    ¬ ∀ a, (coordPolicy 1 0).prob a = jointProb σ 1 0 a := by
  intro hσ
  have h00 := hσ ![0, 0]
  have h01 := hσ ![0, 1]
  have h11 := hσ ![1, 1]
  simp only [coordPolicy, jointProb, Fin.prod_univ_two] at h00 h01 h11
  norm_num at h00 h01 h11
  -- h00 : 1/2 = p q, h01 : 0 = p q', h11 : 1/2 = p' q'
  rcases h01 with h | h <;> simp [h] at h00 h11

end StatisticalRL.Ch7Rest.Marl76
